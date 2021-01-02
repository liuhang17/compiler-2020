#include "allocate_register.hpp"

#include <algorithm>
#include <cmath>
#include <map>
#include <optional>
#include <set>
#include <queue>

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


#define SIMPLE_ALLOCATED_ALGORITHM
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
std::map<MachineInst, int> number_all_inst(MachineFunc *func) {
  std::map<MachineInst, int> num;
  int count = 0;
  for (MachineBB *bb = f->bb.head; bb; bb = bb->next) {
        for (MachineInst *inst = bb->insts.head; inst; inst = inst->next){
          num.insert(*inst,count);
          count++;
        }
  }
  return num;
}
void get_live_internal(std::map<MachineInst, int>& inst_number, std::map<MachineOperand, int>& interval_start,std::map<MachineOperand, int>& interval_end){
  std::map<MachineInst, int>::iterator it = inst_number.begin();
  while(it != inst_number.end()){
    MachineInst tmp = it->first();
    auto [def, use] = get_def_use_ptr(&tmp);
    if(!interval_start.find(*def)){
      interval_start.insert(*def, inst_number[tmp]);
      interval_end.insert(*def, inst_number[tmp]);
    }
    else{
      interval_end[*def] = inst_number[tmp];
    }
    it++;
  }
  for (MachineBB *bb = f->bb.head; bb; bb = bb->next) {
        for (MachineInst *inst = bb->insts.tail; inst; inst = inst->prev) {
          auto [def, use] = get_def_use_ptr(inst);
          for (MachineOperand *oper : use){
            if(interval_start[*oper] > inst_number[*inst]){
              interval_start[*oper] = inst_number[*inst];
            }
            if(interval_end[*oper] < inst_number[*inst]){
              interval_end[*oper] = inst_number[*inst];
            }
          }

        }
      }

}
void linear_allocated(MachineOperand *oper,std::set<MachineOperand> &sp) {
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
      std::map<MachineInst, int> inst_number= number_all_inst(f);
      std::map<MachineOperand, int> interval_start;
      std::map<MachineOperand, int> interval_end;
      get_live_internal(inst_number,interval_start,interval_end);
      std::map<MachineOperand, i32> allocated;
      std::map<i32,bool> empty_reg;
      for(int i = 4;i < 12;i++){
        empty_reg.insert(i, true);
      }
      // std::queue<MachineOperand> live_still;
      // std::map<MachineOperand, int>::iterator it1 = interval_start.begin();
      """
      while(it1 != interval_start.end()){
        live_still.push(it1->first());
        it1++;
      }
      """
      std::map<MachineOperand, int>::iterator it2 = interval_start.begin();
      MachineOperand min_end;
      while(it2 != interval_start.end()){
        MachineInst tmp = &(it2->first());
        if (tmp->state == MachineOperand::State::Virtual) {
          std::map<MachineOperand, i32>::iterator it_allocated = allocated.begin();
          min_end = it_allocated->first;
          while(it_allocated != interval_start.end()){
            MachineOperand allocated_oper = it_allocated->first;
            if(interval_end[allocated_oper] <= interval_start[tmp]){
              allocated.erase(it_allocated);
              empty_reg[allocated[allocated_oper]] = true;
            }
            if(interval_end[min_end] > interval_end[allocated_oper]){
              min_end = allocate_register;
            }
            it_allocated++;
          }
          //delete all finished operand

          if(allocated.size == 8){
            spilled_nodes.insert(min_end);
            empty_reg[allocated[min_end]] = true;
          }
          for(int i = 4;i < 12;i++){
            if(empty_reg[i] == true){
              tmp->state = MachineOperand::State::Allocated;
              tmp->value = i; 
              allocated.insert(tmp, i);
              empty_reg[i] = false;
            }
          }
"""       
          auto p = allocated.find(*tmp);
          int id;
          if (p == allocated.end()) {
            spilled_nodes.insert()  // 如果我们无法为每一个变量分配一个寄存器，则直接panic..
            id = allocated[*oper] = curid++;
          }else id = p->second;
          oper->state = MachineOperand::State::Allocated;
          oper->value = id;
          """
      }
        it2++;
      }



      """
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
    """
      if (spilled_nodes.empty()) {
        done = true;
      } else {
        done = false;
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