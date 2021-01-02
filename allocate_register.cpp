#include "allocate_register.hpp"

#include <algorithm>
#include <cmath>
#include <map>
#include <optional>
#include <set>

#include "../ir/cfg.hpp"

/********************************
 * 寄存器分配文件，请修改此文件完成寄存器分配工作
 * 请认真阅读工程源码，尤其是本文件的辅助函数src/structure/machine_code.cpp
 */ 

// 返回一条机器指令需要使用和修改的寄存器
std::pair<std::vector<MachineOperand>, std::vector<MachineOperand>> get_def_use(MachineInst *inst) {
  std::vector<MachineOperand> def;
  std::vector<MachineOperand> use;

  if (auto x = dyn_cast<MIBinary>(inst)) {
    def = {x->dst};
    use = {x->lhs, x->rhs};
  } else if (auto x = dyn_cast<MILongMul>(inst)) {
    def = {x->dst};
    use = {x->lhs, x->rhs};
  } else if (auto x = dyn_cast<MIFma>(inst)) {
    def = {x->dst};
    use = {x->dst, x->lhs, x->rhs, x->acc};
  } else if (auto x = dyn_cast<MIMove>(inst)) {
    def = {x->dst};
    use = {x->rhs};
  } else if (auto x = dyn_cast<MILoad>(inst)) {
    def = {x->dst};
    use = {x->addr, x->offset};
  } else if (auto x = dyn_cast<MIStore>(inst)) {
    use = {x->data, x->addr, x->offset};
  } else if (auto x = dyn_cast<MICompare>(inst)) {
    use = {x->lhs, x->rhs};
  } else if (auto x = dyn_cast<MICall>(inst)) {
    // args (also caller save)
    for (u32 i = (u32)ArmReg::r0; i < (u32)ArmReg::r0 + std::min(x->func->params.size(), (size_t)4); ++i) {
      use.push_back(MachineOperand::R((ArmReg)i));
    }
    for (u32 i = (u32)ArmReg::r0; i <= (u32)ArmReg::r3; i++) {
      def.push_back(MachineOperand::R((ArmReg)i));
    }
    def.push_back(MachineOperand::R(ArmReg::lr));
    def.push_back(MachineOperand::R(ArmReg::ip));
  } else if (auto x = dyn_cast<MIGlobal>(inst)) {
    def = {x->dst};
  } else if (isa<MIReturn>(inst)) {
    // ret
    use.push_back(MachineOperand::R(ArmReg::r0));
  }
  return {def, use};
}

// 返回一条机器指令需要使用和修改的寄存器的地址
std::pair<MachineOperand *, std::vector<MachineOperand *>> get_def_use_ptr(MachineInst *inst) {
  MachineOperand *def = nullptr;
  std::vector<MachineOperand *> use;

  if (auto x = dyn_cast<MIBinary>(inst)) {
    def = &x->dst;
    use = {&x->lhs, &x->rhs};
  } else if (auto x = dyn_cast<MILongMul>(inst)) {
    def = &x->dst;
    use = {&x->lhs, &x->rhs};
  } else if (auto x = dyn_cast<MIFma>(inst)) {
    def = {&x->dst};
    use = {&x->dst, &x->lhs, &x->rhs, &x->acc};
  } else if (auto x = dyn_cast<MIMove>(inst)) {
    def = &x->dst;
    use = {&x->rhs};
  } else if (auto x = dyn_cast<MILoad>(inst)) {
    def = &x->dst;
    use = {&x->addr, &x->offset};
  } else if (auto x = dyn_cast<MIStore>(inst)) {
    use = {&x->data, &x->addr, &x->offset};
  } else if (auto x = dyn_cast<MICompare>(inst)) {
    use = {&x->lhs, &x->rhs};
  } else if (isa<MICall>(inst)) {
    // intentionally blank
  } else if (auto x = dyn_cast<MIGlobal>(inst)) {
    def = {&x->dst};
  }
  return {def, use};
}

/********************************
 * 分析live-range
 */ 
void liveness_analysis(MachineFunc *f) {
  // calculate LiveUse and Def sets for each bb
  // each elements is a virtual register or precolored register
  for (auto bb = f->bb.head; bb; bb = bb->next) {
    bb->liveuse.clear();
    bb->def.clear();
    for (auto inst = bb->insts.head; inst; inst = inst->next) {
      auto [def, use] = get_def_use(inst);

      // liveuse
      for (auto &u : use) {
        if (u.needs_color() && bb->def.find(u) == bb->def.end()) {
          bb->liveuse.insert(u);
        }
      }
      // def
      for (auto &d : def) {
        if (d.needs_color() && bb->liveuse.find(d) == bb->liveuse.end()) {
          bb->def.insert(d);
        }
      }
    }
    // initial values
    bb->livein = bb->liveuse;
    bb->liveout.clear();
  }

  // calculate LiveIn and LiveOut for each bb
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto bb = f->bb.head; bb; bb = bb->next) {
      std::set<MachineOperand> new_out;
      for (auto &succ : bb->succ) {
        if (succ) {
          new_out.insert(succ->livein.begin(), succ->livein.end());
        }
      }

      if (new_out != bb->liveout) {
        changed = true;
        bb->liveout = new_out;
        std::set<MachineOperand> new_in = bb->liveuse;
        for (auto &e : bb->liveout) {
          if (bb->def.find(e) == bb->def.end()) {
            new_in.insert(e);
          }
        }

        bb->livein = new_in;
      }
    }
  };
}


#define MY_ALLOCATED_ALGORITHM
// 最暴力的寄存器分配策略： 尝试为每一个变量分配一个寄存器，如果变量超过寄存器个数则直接放弃。
#ifdef SIMPLE_ALLOCATED_ALGORITHM
void simple_allocated(MachineOperand *oper) {
  static int curid = 5;
  static int maxid = 31;
  static std::map<MachineOperand, i32> allocated;
  if (oper->state == MachineOperand::State::Virtual) {
    auto p = allocated.find(*oper);
    int id;
    if (p == allocated.end()) {
      assert(curid < maxid);  // 如果我们无法为每一个变量分配一个寄存器，则直接panic..
      id = allocated[*oper] = curid++;
    }else id = p->second;
    oper->state = MachineOperand::State::Allocated;
    oper->value = id;
  }
}
#endif
// iterated register coalescing
void allocate_register(MachineProgram *p) {
  for (auto f = p->func.head; f; f = f->next) {
    auto loop_info = compute_loop_info(f->func);
    dbg(f->func->func->name);
    bool done = false;
    std::set<MachineOperand> spilled_nodes;
    while (!done) {
      liveness_analysis(f);
      spilled_nodes.clear();

      // TODO : 你需要修改这一部分来确定给寄存器分配和染色。
    #ifdef SIMPLE_ALLOCATED_ALGORITHM
      for (MachineBB *bb = f->bb.head; bb; bb = bb->next) {
        for (MachineInst *inst = bb->insts.head; inst; inst = inst->next) {
          auto [def, use] = get_def_use_ptr(inst);
          if (def != nullptr) simple_allocated(def);
          for (MachineOperand *oper : use)
            simple_allocated(oper);
        }
      }
    #endif

    #ifdef MY_ALLOCATED_ALGORITHM
      //对控制流图线性化并对每条指令编号
      std::set<MachineBB*> visited;
      std::vector<MachineBB*> dfs;
      std::vector<MachineBB*> stack;

      stack.push_back(f->bb.head);
      visited.insert(f->bb.head);
      while(!stack.empty()){
        auto temp = stack[stack.size() - 1];
        dfs.push_back(temp);
        stack.pop_back();
        for(int i = 1;i >= 0;i--){
          if(temp->succ[i] != nullptr && visited.find(temp->succ[i]) == visited.end()){
            stack.push_back(temp->succ[i]);
            visited.insert(temp->succ[i]);
          }
        }
      }

      std::map<MachineInst*,int> inst2int;
      int instnum = 0;

      for(int i = 0;i < dfs.size();i++){
        auto bb = dfs[i];
        for(auto inst = bb->insts.head;inst;inst = inst->next){
          instnum++;
          int id = instnum;
          inst2int.insert(std::make_pair(inst,id));
        }
      }

      //计算live interval : inst 粒度
      std::map<MachineOperand*,int> operand2start;
      std::map<MachineOperand*,int> operand2end;
      std::map<MachineOperand,i32> allocated;
      std::map<MachineOperand,std::vector<MachineOperand*>> inverse_ptr;
      std::vector<MachineOperand*> start_list;

      for(int i = 0;i < dfs.size();i++){
        auto bb = dfs[i];
        for (MachineInst *inst = bb->insts.head; inst; inst = inst->next) {
          auto [def, use] = get_def_use_ptr(inst);
          if (def != nullptr){
            operand2start.insert(std::make_pair(def,inst2int[inst]));
            operand2end.insert(std::make_pair(def,inst2int[inst]));
            start_list.push_back(def);
            if(inverse_ptr.find(*def) == inverse_ptr.end()){
              std::vector<MachineOperand*> temp;
              temp.push_back(def);
              inverse_ptr.insert(std::make_pair(*def,temp));
            }
            else{
              //assert(inverse_ptr.find(*def) == inverse_ptr.end());
              //看看是不是会有重复的def使用相同的virtual reg  //确实没报错，说明这一块并没有被执行
              inverse_ptr.find(*def)->second.push_back(def);
            }
          }
        }
      }

      for(int i = 0;i < dfs.size();i++){
        auto bb = dfs[i];
        auto live = bb->liveout;
        for(auto inst = bb->insts.tail;inst; inst = inst->prev){
          for(auto live_var = live.begin(); live_var != live.end();live_var++){
            if(inverse_ptr.find(*live_var) != inverse_ptr.end()){
              auto v = inverse_ptr.find(*live_var)->second;
              for(int k = 0;k < v.size();k++){
                if(operand2end.find(v[k]) != operand2end.end() && (operand2end.find(v[k])->second < inst2int[inst])){
                  operand2end.find(v[k])->second = inst2int[inst];
                }
                if(operand2start.find(v[k]) != operand2start.end() && (operand2start.find(v[k])->second > inst2int[inst])){
                  operand2start.find(v[k])->second = inst2int[inst];
                }
              }
            }
          }


          auto [def, use] = get_def_use_ptr(inst);
          if(def != nullptr){
            live.erase(*def);
          }
          for (MachineOperand *oper : use){
            live.insert(*oper);
          }
        }
      }

      //线性扫描法分配
      // 4-12  bug：并非按头部顺序扫描
      int used[13];
      for(int i = 0;i < 13;i++){
        used[i] = 0;
      }

      for(auto i = 0;i < dfs.size();i++){
        auto bb = dfs[i];
        for(auto inst = bb->insts.head;inst;inst = inst->next){
          auto [def, use] = get_def_use_ptr(inst);
          if((def != nullptr)&&((def->state == MachineOperand::State::Allocated) || (def->state == MachineOperand::State::PreColored))){
            if(def->value < 13 && def->value >= 0){
              used[def->value] = 1;
            }
          }
          for (MachineOperand *oper : use){
            if((oper->state == MachineOperand::State::Allocated) || (oper->state == MachineOperand::State::PreColored)){
              if(oper->value < 13 && oper->value >= 0){
                used[oper->value] = 1;
              }
            }
          }
        }
      }

      std::vector<MachineOperand*> active;
      std::map<MachineOperand*,int> alloc;

      for(int i = start_list.size() - 1;i > 0;i--){
        for(int j = 0;j < i;j++){
          auto a = start_list[j];
          auto b = start_list[j + 1];
          if(operand2start.find(a)->second > (operand2start.find(b)->second)){
            start_list[j + 1] = a;
            start_list[j] = b;
          }
        }
      }

      for(int i = 0;i < start_list.size();i++){
        auto def = start_list[i];
        if(def->state == MachineOperand::State::Virtual){
          //expire old intervals
          int expire = 0;
          for(int k = 0;k < active.size();k++){
            if(operand2end.find(active[k])->second >= (operand2start.find(def)->second)){
              break;
            }
            expire++;
            used[active[k]->value] = 0;
          }
          if(expire > 0){
            active.erase(active.begin(),active.begin() + expire);
          }

          auto p = allocated.find(*def);
          int id = -1;
          if (p == allocated.end()) {
            for(int k = 4;k < 13;k++){
              if(used[k] == 0){
                id = k;
                break;
              }
            }
            if(id == -1){
              //需要spill
              int active_last = operand2end.find(active[active.size() - 1])->second;
              int now_last = operand2end.find(def)->second;
              if(now_last > active_last){
                spilled_nodes.insert(*def);
              }
              else{
                auto sp_node = active[active.size() - 1];
                active[active.size() - 1] = def;
                for(int k = active.size() - 1;k > 0;k--){
                  if(operand2end.find(active[k])->second < (operand2end.find(active[k - 1])->second)){
                    auto temp = active[k];
                    active[k] = active[k - 1];
                    active[k - 1] = temp;
                  }
                }
                id = sp_node->value;
                allocated[*def] = id;
                sp_node->state = MachineOperand::State::Virtual;
                sp_node->value = alloc.find(sp_node)->second;
                alloc.erase(sp_node);
                allocated.erase(*sp_node);
                spilled_nodes.insert(*sp_node);
              }
            }
            else{
              //不需要spill,id即可
              allocated[*def] = id;
              used[id] = 1;
              active.push_back(def);
              for(int k = active.size() - 1;k > 0;k--){
                if(operand2end.find(active[k])->second < (operand2end.find(active[k - 1])->second)){
                  auto temp = active[k];
                  active[k] = active[k - 1];
                  active[k - 1] = temp;
                }
              }
            }
          }else {
            //这里测试，每个def都需要重新分配 //确实如此，这个是白费的
            //assert(0 == 1);
            id = p->second;
          }
          if(id != -1){
            def->state = MachineOperand::State::Allocated;
            alloc.insert(std::make_pair(def,def->value));
            def->value = id;
          }         
        }
      }

      for(int i = 0;i < dfs.size();i++){
        auto bb = dfs[i];
        for (MachineInst *inst = bb->insts.head; inst; inst = inst->next) {
          auto [def, use] = get_def_use_ptr(inst);
          for (MachineOperand *oper : use){
            if (oper->state == MachineOperand::State::Virtual) {
              auto p = allocated.find(*oper);
              int id;
              if (p == allocated.end()) {
                spilled_nodes.insert(*oper);
              }else {
                id = p->second;
                oper->state = MachineOperand::State::Allocated;
                alloc.insert(std::make_pair(oper,oper->value));
                oper->value = id;
              }
            }
          }
        }
      }      
    #endif

      if (spilled_nodes.empty()) {
        done = true;
      } else {
        done = false;
        
        for(auto iter = alloc.begin();iter != alloc.end();iter++){
          iter->first->state = MachineOperand::State::Virtual;
          iter->first->value = iter->second;
        }
        
        for (auto &n : spilled_nodes) {
          auto spill = "Spilling v" + std::to_string(n.value);
          dbg(spill);
          // allocate on stack
          for (auto bb = f->bb.head; bb; bb = bb->next) {
            auto offset = f->stack_size;
            auto offset_imm = MachineOperand::I(offset);

            auto generate_access_offset = [&](MIAccess *access_inst) {
              if (offset < (1u << 12u)) {  // ldr / str has only imm12
                access_inst->offset = offset_imm;
              } else {
                auto mv_inst = new MIMove(access_inst);  // insert before access
                mv_inst->rhs = offset_imm;
                mv_inst->dst = MachineOperand::V(f->virtual_max++);
                access_inst->offset = mv_inst->dst;
              }
            };

            // generate a MILoad before first use, and a MIStore after last def
            MachineInst *first_use = nullptr;
            MachineInst *last_def = nullptr;
            i32 vreg = -1;
            auto checkpoint = [&]() {
              if (first_use) {
                auto load_inst = new MILoad(first_use);
                load_inst->bb = bb;
                load_inst->addr = MachineOperand::R(ArmReg::sp);
                load_inst->shift = 0;
                generate_access_offset(load_inst);
                load_inst->dst = MachineOperand::V(vreg);
                first_use = nullptr;
              }

              if (last_def) {
                auto store_inst = new MIStore();
                store_inst->bb = bb;
                store_inst->addr = MachineOperand::R(ArmReg::sp);
                store_inst->shift = 0;
                bb->insts.insertAfter(store_inst, last_def);
                generate_access_offset(store_inst);
                store_inst->data = MachineOperand::V(vreg);
                last_def = nullptr;
              }
              vreg = -1;
            };

            int i = 0;
            for (auto orig_inst = bb->insts.head; orig_inst; orig_inst = orig_inst->next) {
              auto [def, use] = get_def_use_ptr(orig_inst);
              if (def && *def == n) {
                // store
                if (vreg == -1) {
                  vreg = f->virtual_max++;
                }
                def->value = vreg;
                last_def = orig_inst;
              }

              for (auto &u : use) {
                if (*u == n) {
                  // load
                  if (vreg == -1) {
                    vreg = f->virtual_max++;
                  }
                  u->value = vreg;
                  if (!first_use && !last_def) {
                    first_use = orig_inst;
                  }
                }
              }

              if (i++ > 30) {
                // don't span vreg for too long
                checkpoint();
              }
            }

            checkpoint();
          }
          f->stack_size += 4;  // increase stack size
        }
      }
    }
  }
}