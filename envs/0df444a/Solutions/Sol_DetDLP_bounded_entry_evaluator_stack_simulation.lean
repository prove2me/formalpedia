-- Prove2me | solution 1 for DetDLP.bounded_entry_evaluator_stack_simulation
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T15:54:14.678609+00:00
-- url     : https://prove2.me/submissions/969b66dc-8710-46aa-a676-573458732677

import Definitions.Def_DetDLP_Machine
import Definitions.Def_OAIQ081S000

section

namespace DetDLP.EntryTapeModel
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Turing
abbrev Symbol := Option Bool

structure Cells where
  left : List Symbol
  head : Symbol
  right : List Symbol
  deriving DecidableEq

def Cells.tape (a : Cells) : Tape Symbol := ⟨a.head,ListBlank.mk a.left,ListBlank.mk a.right⟩
def Cells.act (a : Cells) : TM0.Stmt Symbol → Cells
  | .write c => {a with head := c}
  | .move .left => ⟨a.left.tail,a.left.headI,a.head::a.right⟩
  | .move .right => ⟨a.head::a.left,a.right.headI,a.right.tail⟩
def tapeAct (a : Tape Symbol) : TM0.Stmt Symbol→Tape Symbol
  | .write c => a.write c
  | .move d => a.move d

theorem act_ok (a : Cells) (s : TM0.Stmt Symbol) : (a.act s).tape = tapeAct a.tape s := by
  cases s with
  | write c => rfl
  | move d => cases d <;> rfl

def Cells.init (w : List Bool) : Cells := ⟨[],(w.map some).headI,(w.map some).tail⟩
theorem init_ok (w : List Bool) : (Cells.init w).tape=Tape.mk₁ (w.map some) := rfl

def Fits (a : Cells) (pos lo hi : ℤ) : Prop :=
  pos-lo=(a.left.length:ℤ) ∧ hi-pos=(a.right.length:ℤ)

theorem fits_act (a : Cells) (s : TM0.Stmt Symbol) {pos lo hi : ℤ} (h : Fits a pos lo hi) :
    let next := pos+headDisplacement s
    Fits (a.act s) next (min lo next) (max hi next) := by
  obtain ⟨hl,hr⟩ := h
  cases s with
  | write c => simp [Fits,Cells.act,headDisplacement,min_eq_left (show lo≤pos by omega),max_eq_left (show pos≤hi by omega),hl,hr]
  | move d =>
    cases d <;> simp only [Fits,Cells.act,headDisplacement,List.length_cons,List.length_tail,Nat.cast_add,Nat.cast_one] <;> omega

variable (E : PrimitiveMachine)
abbrev Tapes := Fin E.tapeCount→Cells
def init (w : List Bool) : Tapes E := fun i => Cells.init (if i=E.inputTape then w else [])
def Represents (a : Tapes E) (c : LocatedCfg E) : Prop := ∀ i,
  (a i).tape=c.config.tapes i ∧ Fits (a i) (c.position i) (c.lower i) (c.upper i)

theorem init_rep (w : List Bool) : Represents E (init E w) (locatedInit E w) := by
  intro i; by_cases h : i=E.inputTape
  · subst i; simp [init,init_ok,locatedInit,PrimitiveMachine.init,Fits,Cells.init,List.length_tail] <;> rfl
  · simp [init,h,init_ok,locatedInit,PrimitiveMachine.init,Fits,Cells.init] <;> rfl

theorem total_space {a : Tapes E} {c : LocatedCfg E} (ha : Represents E a c) :
    (∑ i,((a i).left.length+1+(a i).right.length))=visitedSpace c := by
  apply Finset.sum_congr rfl; intro i _
  obtain ⟨_,hl,hr⟩ := ha i; omega

theorem one_step {a : Tapes E} {c c' : LocatedCfg E} (ha : Represents E a c) {q : Fin E.stateCount}
    (hq : c.config.state=.inr q) (step : locatedStep E c=some c') :
    let i := E.scan q
    match E.transition q (a i).head with
    | .inl b => c'.config.state=.inl b ∧ Represents E a c'
    | .inr (t,s) => c'.config.state=.inr t ∧ Represents E (Function.update a i ((a i).act s)) c' := by
  intro i
  have head : (a i).head=(c.config.tapes i).head := congrArg Tape.head (ha i).1
  rw [head]
  rcases h : E.transition q (c.config.tapes i).head with b|⟨t,s⟩
  · simp only [locatedStep,PrimitiveMachine.step,hq,i,h,Option.map_some,Option.some.injEq] at step
    subst c'; simp only [LocatedCfg.monitor,hq,Sum.elim_inr,i,h,Sum.elim_inl]
    exact ⟨trivial,ha⟩
  · simp only [locatedStep,PrimitiveMachine.step,hq,i,h,Option.map_some,Option.some.injEq] at step
    subst c'; simp only [LocatedCfg.monitor,hq,Sum.elim_inr,i,h]
    refine ⟨trivial,?_⟩
    intro j
    by_cases hj : j=E.scan q
    · subst j; simp only [Function.update_self,act_ok]
      refine ⟨?_,fits_act _ _ (ha i).2⟩
      rw [(ha (E.scan q)).1]; cases s <;> rfl
    · simpa only [Function.update_of_ne hj] using ha j

end DetDLP.EntryTapeModel
end

section

namespace DetDLP.EntryTapeCode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram EntryTapeModel Turing
variable (E : PrimitiveMachine)
abbrev Index := Fin E.tapeCount
abbrev Heads := Index E→Symbol
abbrev Lane := Index E×Bool×Bool
abbrev Label := (Index E→Symbol)×Fin E.stateCount×Fin 8
noncomputable def slot := Fintype.equivFin (Lane E)
noncomputable def addr := Fintype.equivFin (Label E)
abbrev S := Fintype.card (Lane E)
abbrev L := Fintype.card (Label E)
abbrev Regs := Fin 3→Bool
abbrev Bank := Fin (S E)→List Bool
abbrev Code := Instr 3 (S E) (L E)
abbrev Conf := Cfg 3 (S E) (L E)
noncomputable def lane (i : Index E) (left tag : Bool) := slot E (i,left,tag)
noncomputable def pc (h : Heads E) (q : Fin E.stateCount) (k : Fin 8) := addr E (h,q,k)
def bit (tag : Bool) (c : Symbol) := if tag then c.isSome else c.getD false
def half (a : Cells) (left : Bool) := if left then a.left else a.right
noncomputable def store (a : Tapes E) : Bank E := fun j =>
  let v := (slot E).symm j
  (half (a v.1) v.2.1).map (bit v.2.2)
theorem store_at (a : Tapes E) (i : Index E) (d b : Bool) :
    store E a (lane E i d b)=(half (a i) d).map (bit b) := by simp [store,lane]

noncomputable def command (out : Index E) (h : Heads E) (q : Fin E.stateCount) (k : Fin 8) : Code E :=
  let i := E.scan q
  let jump := pc E h q
  match E.transition q (h i) with
  | .inl _ =>
    match k.val with
    | 0 => .set 0 (bit true (h out)) (jump 1)
    | 1 => .push (lane E out false true) 0 (jump 2)
    | 2 => .set 0 (bit false (h out)) (jump 3)
    | 3 => .push (lane E out false false) 0 (jump 4)
    | _ => .halt
  | .inr (t, .write c) => .goto (pc E (Function.update h i c) t 0)
  | .inr (t, .move dir) =>
    let d := match dir with | .left => true | .right => false
    let next (c : Symbol) := pc E (Function.update h i c) t 0
    match k.val with
    | 0 => .set 0 (bit true (h i)) (jump 1)
    | 1 => .push (lane E i (!d) true) 0 (jump 2)
    | 2 => .set 0 (bit false (h i)) (jump 3)
    | 3 => .push (lane E i (!d) false) 0 (jump 4)
    | 4 => .pop (lane E i d true) 0 2 (jump 5)
    | 5 => .pop (lane E i d false) 1 2 (jump 6)
    | 6 => .branch 0 (jump 7) (next none)
    | _ => .branch 1 (next (some true)) (next (some false))

noncomputable def program (out : Index E) (initialHeads : Heads E) : Program 3 (S E) (L E) where
  inputStack := lane E E.inputTape false false
  outputStack := lane E out false false
  entry := pc E initialHeads E.start 0
  code j := let v := (addr E).symm j
            command E out v.1 v.2.1 v.2.2

abbrev machineHeads (a : Tapes E) : Heads E := fun i => (a i).head
noncomputable def cf (h : Heads E) (q : Fin E.stateCount) (k : Fin 8) (r : Regs) (b : Bank E) : Conf E :=
  ⟨some (pc E h q k),r,b⟩
theorem step_at (out : Index E) (start h : Heads E) (q : Fin E.stateCount) (k : Fin 8) (r : Regs) (b : Bank E) :
    BitProgram.step (program E out start) (cf E h q k r b)=
      some (execInstr (command E out h q k) (cf E h q k r b)) := by
  simp [cf,program,BitProgram.step,pc]

theorem store_write (a : Tapes E) (i : Index E) (c : Symbol) :
    store E (Function.update a i ((a i).act (.write c)))=store E a := by
  funext j
  obtain ⟨⟨i',d,b⟩,rfl⟩ := (slot E).surjective j
  change store E _ (lane E i' d b)=store E _ (lane E i' d b)
  rw [store_at,store_at]
  by_cases hi : i'=i
  · subst i'; rw [Function.update_self]; cases d <;> rfl
  · rw [Function.update_of_ne hi]

theorem heads_update (a : Tapes E) (i : Index E) (c : Cells) :
    machineHeads E (Function.update a i c)=Function.update (machineHeads E a) i c.head := by
  funext j; by_cases h : j=i <;> simp [machineHeads,Function.update_apply,h]

theorem write_step (out : Index E) (start : Heads E) (a : Tapes E)
    (q t : Fin E.stateCount) (c : Symbol) (r : Regs)
    (hc : E.transition q ((a (E.scan q)).head)=.inr (t,.write c)) :
    let b := Function.update a (E.scan q) ((a (E.scan q)).act (.write c))
    BitProgram.Trace (program E out start) 1 (cf E (machineHeads E a) q 0 r (store E a))
      (cf E (machineHeads E b) t 0 r (store E b)) := by
  intro b
  refine .cons ?_ (.refl _)
  rw [step_at]
  simp only [command,machineHeads,hc]
  rw [show store E b=store E a from store_write E ..,show machineHeads E b=_ from heads_update E ..]
  rfl

end DetDLP.EntryTapeCode
end

section

namespace DetDLP.EntryTapeCode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram EntryTapeModel Turing
variable (E : PrimitiveMachine)
@[simp] theorem lane_eq (i j : Index E) (d e b c : Bool) :
    lane E i d b=lane E j e c ↔ i=j ∧ d=e ∧ b=c := by simp [lane]
def side : Dir→Bool | .left => true | .right => false
noncomputable def pushTag (a : Tapes E) (i : Index E) (d : Bool) : Bank E :=
  Function.update (store E a) (lane E i (!d) true)
    (bit true (a i).head :: (half (a i) (!d)).map (bit true))
noncomputable def pushed (a : Tapes E) (i : Index E) (d : Bool) : Bank E :=
  Function.update (pushTag E a i d) (lane E i (!d) false)
    (bit false (a i).head :: (half (a i) (!d)).map (bit false))
noncomputable def popTag (a : Tapes E) (i : Index E) (d : Bool) : Bank E :=
  Function.update (pushed E a i d) (lane E i d true) ((half (a i) d).map (bit true)).tail
noncomputable def popped (a : Tapes E) (i : Index E) (d : Bool) : Bank E :=
  Function.update (popTag E a i d) (lane E i d false) ((half (a i) d).map (bit false)).tail

theorem store_move (a : Tapes E) (i : Index E) (dir : Dir) :
    popped E a i (side dir)=store E (Function.update a i ((a i).act (.move dir))) := by
  funext j
  obtain ⟨⟨j,d,b⟩,rfl⟩ := (slot E).surjective j
  change popped E a i (side dir) (lane E j d b)=store E _ (lane E j d b)
  by_cases hi : i=j
  · subst j; cases dir <;> cases d <;> cases b <;>
      simp [popped,popTag,pushed,pushTag,side,Function.update_apply,store_at,half,Cells.act,List.map_tail]
  · cases dir <;> cases d <;> cases b <;>
      simp [popped,popTag,pushed,pushTag,side,Function.update_apply,store_at,hi,Ne.symm hi]

theorem get_head (x : List Symbol) (b : Bool) : ((x.map (bit b)).head?).getD false=bit b x.headI := by
  cases x <;> cases b <;> rfl

theorem move_trace (out : Index E) (start : Heads E) (a : Tapes E)
    (q t : Fin E.stateCount) (dir : Dir) (r : Regs)
    (hc : E.transition q ((a (E.scan q)).head)=.inr (t,.move dir)) :
    let i := E.scan q
    let b := Function.update a i ((a i).act (.move dir))
    ∃ k≤8,∃ r',BitProgram.Trace (program E out start) k (cf E (machineHeads E a) q 0 r (store E a))
      (cf E (machineHeads E b) t 0 r' (store E b)) := by
  intro i b
  let P := program E out start
  let h := machineHeads E a
  let d := side dir
  let U := half (a i) d
  let r1 := Function.update r (0:Fin 3) (bit true (h i))
  let r2 := Function.update r1 (0:Fin 3) (bit false (h i))
  let r3 := readRegs r2 0 2 ((U.map (bit true)).head?)
  let r4 := readRegs r3 1 2 ((U.map (bit false)).head?)
  let F := cf E h q
  have st (k : Fin 8) (v : Regs) (A : Bank E) :
      BitProgram.step P (F k v A)=some (execInstr (command E out h q k) (F k v A)) :=
    step_at E out start h q k v A
  have ht : E.transition q (h (E.scan q))=.inr (t,.move dir) := hc
  have s0 : BitProgram.step P (F 0 r (store E a))=some (F 1 r1 (store E a)) := by
    rw [st]; simp [command,ht,cf,F,r1,i,execInstr]
  have s1 : BitProgram.step P (F 1 r1 (store E a))=some (F 2 r1 (pushTag E a i d)) := by
    rw [st]; cases dir <;> simp [command,ht,cf,F,execInstr,pushTag,store_at,r1,i,d,side,h,machineHeads]
  have s2 : BitProgram.step P (F 2 r1 (pushTag E a i d))=some (F 3 r2 (pushTag E a i d)) := by
    rw [st]; simp [command,ht,cf,F,r2,i,execInstr]
  have s3 : BitProgram.step P (F 3 r2 (pushTag E a i d))=some (F 4 r2 (pushed E a i d)) := by
    rw [st]; cases dir <;> simp [command,ht,cf,F,execInstr,pushed,pushTag,Function.update_apply,store_at,r2,i,d,side,h,machineHeads]
  have s4 : BitProgram.step P (F 4 r2 (pushed E a i d))=some (F 5 r3 (popTag E a i d)) := by
    rw [st]; cases dir <;> simp [command,ht,cf,F,execInstr,popTag,pushed,pushTag,Function.update_apply,store_at,r3,U,i,d,side]
  have s5 : BitProgram.step P (F 5 r3 (popTag E a i d))=some (F 6 r4 (popped E a i d)) := by
    rw [st]; cases dir <;> simp [command,ht,cf,F,execInstr,popped,popTag,pushed,pushTag,Function.update_apply,store_at,r4,U,i,d,side]
  have tag : r4 0=bit true U.headI := by rw [← get_head U true]; simp [r4,r3,readRegs,Function.update_apply]
  have value : r4 1=bit false U.headI := by rw [← get_head U false]; simp [r4,readRegs,Function.update_apply]
  have newHead : ((a i).act (.move dir)).head=U.headI := by cases dir <;> rfl
  have nextH : machineHeads E b=Function.update h i U.headI := (heads_update E a i _).trans (by rw [newHead])
  have bank : store E b=popped E a i d := (store_move E a i dir).symm
  rw [nextH,bank]
  cases z : U.headI with
  | none =>
    refine ⟨7,by decide,r4,.cons s0 (.cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.cons ?_ (.refl _)))))))⟩
    rw [st]; simp [command,ht,execInstr,cf,F,tag,z,bit,i]
  | some v =>
    refine ⟨8,by decide,r4,.cons s0 (.cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.cons (b:=F 7 r4 (popped E a i d)) ?_ (.cons ?_ (.refl _))))))))⟩
    · rw [st]; simp [command,ht,execInstr,cf,F,tag,z,bit]
    · rw [st]; cases v <;> simp [command,ht,execInstr,cf,F,value,z,bit,i]
end DetDLP.EntryTapeCode
end

section

namespace DetDLP.BitTracePolynomial
open OAI.Algorithms.SubexponentialSAT

private theorem instr_grows {r s l : ℕ} (op : BitProgram.Instr r s l) (a : BitProgram.Cfg r s l) (i : Fin s) :
    ((BitProgram.execInstr op a).stacks i).length ≤ (a.stacks i).length+1 := by
  cases op <;> simp [BitProgram.execInstr,Function.update_apply] <;>
    split_ifs <;> simp_all <;> omega

theorem trace_grows {r s l : ℕ} {p : BitProgram.Program r s l} {a b : BitProgram.Cfg r s l}
    {k : ℕ} (h : BitProgram.Trace p k a b) (i : Fin s) :
    (b.stacks i).length ≤ (a.stacks i).length+k := by
  induction h with
  | refl => simp
  | @cons k a c b hs tr ih =>
    obtain ⟨lab,_,he⟩ := Option.map_eq_some_iff.mp hs
    subst c
    have := instr_grows (p.code lab) a i
    omega

theorem initial_grows {r s l : ℕ} {p : BitProgram.Program r s l} {b : BitProgram.Cfg r s l}
    {k : ℕ} {input : List Bool} (h : BitProgram.Trace p k (BitProgram.initial p input) b) (i : Fin s) :
    (b.stacks i).length ≤ input.length+k := by
  apply (trace_grows h i).trans
  simp [BitProgram.initial]; split_ifs <;> simp

theorem absorb_cost (s k u t I : ℕ) (hu : 1 ≤ u)
    (ht : t ≤ (u+2)^k) (hI : I ≤ 100*(u+2)^3) :
    let K := (s+1)*(2*k+300)
    7*t ≤ K*(u+1)^K ∧ s*(I+t+I+15) ≤ K*(u+1)^K := by
  intro K
  have hk : 2*k ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s]
  have hc : 6 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  have hb : u+2 ≤ (u+1)^2 := by nlinarith only [hu,Nat.zero_le (u^2)]
  have comp (j : ℕ) (hj : 2*j ≤ K) : (u+2)^j ≤ (u+1)^K := by
    calc
      _ ≤ ((u+1)^2)^j := Nat.pow_le_pow_left hb _
      _ = (u+1)^(2*j) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hj
  let X := (u+1)^K
  have hT : t ≤ X := ht.trans (comp k hk)
  have hIn : I ≤ 100*X := hI.trans (Nat.mul_le_mul_left _ (comp 3 hc))
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hk7 : 7 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  have hsc : s*216 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  refine ⟨Nat.mul_le_mul hk7 hT,?_⟩
  calc
    s*(I+t+I+15) ≤ s*(216*X) := Nat.mul_le_mul_left _ (by omega)
    _ = (s*216)*X := by ring
    _ ≤ K*X := Nat.mul_le_mul_right _ hsc

end DetDLP.BitTracePolynomial
end

section

namespace DetDLP.EntryTapeCode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram EntryTapeModel Turing
variable (E : PrimitiveMachine)

noncomputable def ended (a : Tapes E) (out : Index E) : Bank E := pushed E a out true

theorem halt_trace (out : Index E) (start : Heads E) (a : Tapes E) (q : Fin E.stateCount)
    (answer : Bool) (r : Regs) (hc : E.transition q ((a (E.scan q)).head)=.inl answer) :
    ∃ r',BitProgram.Trace (program E out start) 5 (cf E (machineHeads E a) q 0 r (store E a))
      ⟨none,r',ended E a out⟩ := by
  let h := machineHeads E a
  let A := store E a
  let B := pushTag E a out true
  let C := ended E a out
  let v := Function.update r (0:Fin 3) (bit true (h out))
  let w := Function.update v (0:Fin 3) (bit false (h out))
  let F := cf E h q
  have ht : E.transition q (h (E.scan q))=.inl answer := hc
  refine ⟨w,.cons (b:=F 1 v A) ?_ (.cons (b:=F 2 v B) ?_ (.cons (b:=F 3 w B) ?_
    (.cons (b:=F 4 w C) ?_ (.cons ?_ (.refl _)))))⟩
  all_goals rw [step_at]
  all_goals simp [command,ht,cf,F,A,B,C,ended,pushed,pushTag,store_at,v,w,h,machineHeads,
    execInstr,Function.update_apply]

theorem output_lane (a : Tapes E) (out : Index E) (tag : Bool) :
    ended E a out (lane E out false tag)=((a out).head::(a out).right).map (bit tag) := by
  cases tag <;> simp [ended,pushed,pushTag,Function.update_apply,store_at,half]

def extract : List Bool→List Bool→List Bool
  | true::t,x::v => x::extract t v
  | _,_ => []

def strip : List Symbol→List Bool
  | some b::xs => b::strip xs
  | _ => []

theorem extract_maps (v : List Symbol) : extract (v.map (bit true)) (v.map (bit false))=strip v := by
  induction v with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | none => rfl
    | some b => exact congrArg (b::·) ih

theorem stripped {l : List Symbol} {w : List Bool} (he : ListBlank.mk l=ListBlank.mk (w.map some)) :
    strip l=w := by
  induction w generalizing l with
  | nil =>
    have eq := congrArg ListBlank.head he
    cases l with
    | nil => rfl
    | cons a v => change a=none at eq; subst a; rfl
  | cons b w ih =>
    have eq := congrArg ListBlank.head he
    cases l with
    | nil => change none=some b at eq; contradiction
    | cons a l =>
      change a=some b at eq; subst a
      have e := congrArg ListBlank.tail he
      change ListBlank.mk l=ListBlank.mk (w.map some) at e
      exact congrArg (b::·) (ih e)

theorem output_ok (a : Tapes E) (out : Index E) (w : List Bool) (h : (a out).tape=Tape.mk₁ (w.map some)) :
    extract (ended E a out (lane E out false true)) (ended E a out (lane E out false false))=w := by
  rw [output_lane,output_lane,extract_maps]
  apply stripped
  have e := congrArg Tape.right₀ h
  rw [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀] at e
  exact e

theorem cell_width (a : Tapes E) {c : SqrtLogSpace.LocatedCfg E} (h : Represents E a c) (j : Fin (S E)) :
    (store E a j).length≤SqrtLogSpace.visitedSpace c := by
  obtain ⟨⟨i,d,b⟩,rfl⟩ := (slot E).surjective j
  change (store E a (lane E i d b)).length≤_
  rw [store_at,List.length_map,← total_space E h]
  apply le_trans _ (Finset.single_le_sum (f:=fun i => (a i).left.length+1+(a i).right.length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  cases d <;> simp [half] <;> omega

/-- A trace with a bound at every prefix, suitable for compiling a long polynomial-space run. -/
inductive Safe {r s l : ℕ} (P : Program r s l) (M : ℕ) : ℕ→Cfg r s l→Cfg r s l→Prop
  | refl {u} (width : ∀ j,(u.stacks j).length≤M) : Safe P M 0 u u
  | cons {k u v z} (width : ∀ j,(u.stacks j).length≤M) (step : BitProgram.step P u=some v)
      (rest : Safe P M k v z) : Safe P M (k+1) u z

theorem Safe.trace {r s l M n : ℕ} {P : Program r s l} {a b} (h : Safe P M n a b) : BitProgram.Trace P n a b := by
  induction h with
  | refl => exact .refl _
  | cons _ st _ ih => exact .cons st ih

theorem Safe.join {r s l M n m : ℕ} {P : Program r s l} {a b c} (h : Safe P M n a b) (g : Safe P M m b c) :
    Safe P M (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons w st _ ih => rw [Nat.succ_add]; exact .cons w st (ih g)

theorem Safe.prefix {r s l M n : ℕ} {P : Program r s l} {a b} (h : Safe P M n a b)
    {k c} (hk : k≤n) (tr : BitProgram.Trace P k a c) : ∀ j,(c.stacks j).length≤M := by
  induction h generalizing k c with
  | refl w =>
    obtain rfl : k=0 := by omega
    cases tr
    exact w
  | cons w st rest ih =>
    cases tr with
    | refl => exact w
    | cons st' rest' =>
      have eq := Option.some.inj (st.symm.trans st')
      subst_vars
      exact ih (by omega) rest'

theorem short_safe {r s l M n : ℕ} {P : Program r s l} {a b} (tr : BitProgram.Trace P n a b)
    (bound : ∀ j,(a.stacks j).length+n≤M) : Safe P M n a b := by
  induction tr with
  | refl => exact .refl (by simpa using bound)
  | @cons k a v z st rest ih =>
    apply Safe.cons (fun j => by have := bound j; omega) st
    apply ih; intro j
    have grow := BitTracePolynomial.trace_grows (show BitProgram.Trace P 1 a v from .cons st (.refl _)) j
    have := bound j; omega
end DetDLP.EntryTapeCode
end

section

namespace DetDLP.EntryTapeCode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open BitProgram EntryTapeModel Turing
variable (E : PrimitiveMachine)

theorem stopped {c z : LocatedCfg E} {answer : Bool} (h : c.config.state=.inl answer) {n : ℕ}
    (tr : Computation.Trace (locatedStep E) n c z) : n=0 ∧ c=z := by
  cases tr with
  | refl => exact ⟨rfl,rfl⟩
  | cons st _ => simp [locatedStep,PrimitiveMachine.step,h] at st

theorem simulate {c z : LocatedCfg E} {n : ℕ} (tr : Computation.Trace (locatedStep E) n c z)
    (out : Index E) (start : Heads E) (M : ℕ) {answer : Bool} (halt : z.config.state=.inl answer)
    (space : ∀ k c',k≤n→ Computation.Trace (locatedStep E) k c c'→visitedSpace c'≤M)
    (a : Tapes E) (rep : Represents E a c) (q : Fin E.stateCount) (hq : c.config.state=.inr q) (r : Regs) :
    ∃ b : Tapes E, Represents E b z ∧ ∃ r' k,k≤8*n ∧
      Safe (program E out start) (M+8) k (cf E (machineHeads E a) q 0 r (store E a))
        ⟨none,r',ended E b out⟩ := by
  induction tr generalizing q a r with
  | refl => simp [hq] at halt
  | @cons n c c' z hs tail ih =>
    have width (j) : (store E a j).length≤M := (cell_width E a rep j).trans (space 0 c (by omega) (.refl _))
    have refineStep := one_step E rep hq hs
    let i := E.scan q
    rcases ht : E.transition q ((a i).head) with ans|⟨t,act⟩
    · change (match E.transition q ((a i).head) with
        | .inl b => c'.config.state=.inl b ∧ Represents E a c'
        | .inr (t,s) => c'.config.state=.inr t ∧ Represents E (Function.update a i ((a i).act s)) c') at refineStep
      rw [ht] at refineStep
      obtain ⟨rfl,rfl⟩ := stopped E refineStep.1 tail
      obtain ⟨r',hh⟩ := halt_trace E out start a q ans r ht
      exact ⟨a,refineStep.2,r',5,by decide,short_safe (M:=M+8) hh fun j => by simp only [cf]; have := width j; omega⟩
    · change (match E.transition q ((a i).head) with
        | .inl b => c'.config.state=.inl b ∧ Represents E a c'
        | .inr (t,s) => c'.config.state=.inr t ∧ Represents E (Function.update a i ((a i).act s)) c') at refineStep
      rw [ht] at refineStep
      let b := Function.update a i ((a i).act act)
      have short : ∃ k≤8,∃ r',BitProgram.Trace (program E out start) k
          (cf E (machineHeads E a) q 0 r (store E a)) (cf E (machineHeads E b) t 0 r' (store E b)) := by
        cases act with
        | write v => exact ⟨1,by decide,r,write_step E out start a q t v r ht⟩
        | move d => exact move_trace E out start a q t d r ht
      obtain ⟨k,hk,r',ht'⟩ := short
      have B : ∀ j c'',j≤n→ Computation.Trace (locatedStep E) j c' c''→visitedSpace c''≤M :=
        fun j c'' hj tr => space (j+1) c'' (by omega) (.cons hs tr)
      obtain ⟨final,hr,rf,l,hl,hl'⟩ := ih halt B b refineStep.2 t refineStep.1 r'
      exact ⟨final,hr,rf,k+l,by omega,(short_safe (M:=M+8) ht' fun j => by simp only [cf]; have := width j; omega).join hl'⟩

theorem call (out : Index E) (input output : List Bool) (T M : ℝ) (run : RunsWithin E out input output T M)
    (r : Regs) (start : Heads E) :
    let a := EntryTapeModel.init E input
    ∃ (k : ℕ) (c : Conf E),(k:ℝ)≤8*T ∧ c.pc=none ∧
      extract (c.stacks (lane E out false true)) (c.stacks (lane E out false false))=output ∧
      Safe (program E out start) (⌊M⌋₊+8) k
        (cf E (machineHeads E a) E.start 0 r (store E a)) c := by
  intro a
  obtain ⟨n,z,h,⟨ans,hz⟩,hw,ht,hs⟩ := run
  have space k c (hk : k≤n) (tr : Computation.Trace (locatedStep E) k (locatedInit E input) c) :
      visitedSpace c≤⌊M⌋₊ := Nat.le_floor (hs k c hk tr)
  obtain ⟨b,rb,rf,k,hk,hk'⟩ := simulate E h out start ⌊M⌋₊ hz space a (init_rep E input) E.start rfl r
  refine ⟨k,_,?_,rfl,output_ok E b out output ((rb out).1.trans hw),hk'⟩
  exact (by exact_mod_cast hk : (k:ℝ)≤8*(n:ℝ)).trans (by linarith)
end DetDLP.EntryTapeCode
end

section
namespace DetDLP.EntryTapeCode
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram EntryTapeModel
def firstHeads (E : PrimitiveMachine) : Heads E := fun i => if i=E.inputTape then some true else none
theorem initial_heads (E : PrimitiveMachine) (w : List Bool) :
    machineHeads E (EntryTapeModel.init E (true::w))=firstHeads E := by
  funext i; by_cases h : i=E.inputTape <;> simp [machineHeads,EntryTapeModel.init,Cells.init,h,firstHeads] <;> rfl

theorem first_store (E : PrimitiveMachine) (w : List Bool) :
    store E (EntryTapeModel.init E (true::w)) =
      fun j => if j=lane E E.inputTape false true then List.replicate w.length true else
        if j=lane E E.inputTape false false then w else [] := by
  funext j
  obtain ⟨⟨i,d,b⟩,rfl⟩ := (slot E).surjective j
  change store E _ (lane E i d b)=if lane E i d b=_ then _ else if lane E i d b=_ then _ else _
  rw [store_at]
  by_cases H : i=E.inputTape
  · subst i; cases d <;> cases b <;>
      simp [EntryTapeModel.init,Cells.init,bit,half,List.map_map,Function.comp_def]
  · cases d <;> cases b <;> simp [EntryTapeModel.init,H,Cells.init,half]

theorem extract_eq (tags values : List Bool) :
    extract tags values=(((tags.zip values).takeWhile Prod.fst).map Prod.snd) := by
  induction tags generalizing values with
  | nil => rfl
  | cons b tags ih => cases values with
    | nil => cases b <;> rfl
    | cons x values => cases b <;> simp [extract,ih]

theorem callback (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (Q : Program 3 s l) (it iv ot ov : Fin s), it≠iv ∧ ot≠ov ∧
    ∀ (input output : List Bool) (T M : ℝ),RunsWithin E out (true::input) output T M →
      ∀ r : Fin 3→Bool,
      let initial : Cfg 3 s l := ⟨some Q.entry,r,fun j =>
        if j=it then List.replicate input.length true else if j=iv then input else []⟩
      ∃ (n : ℕ) (final : Cfg 3 s l), (n:ℝ)≤8*T ∧ BitProgram.Trace Q n initial final ∧
        final.pc=none ∧ ((((final.stacks ot).zip (final.stacks ov)).takeWhile Prod.fst).map Prod.snd)=output ∧
        ∀ k c,k≤n→ BitProgram.Trace Q k initial c→∀ j,(c.stacks j).length≤⌊M⌋₊+8 := by
  let Q := program E out (firstHeads E)
  refine ⟨S E,L E,Q,lane E E.inputTape false true,lane E E.inputTape false false,
    lane E out false true,lane E out false false,by simp,by simp,?_⟩
  intro input output T M run r initial
  obtain ⟨k,c,ht,hc,hw,hs⟩ := call E out (true::input) output T M run r (firstHeads E)
  rw [initial_heads,first_store] at hs
  exact ⟨k,c,ht,hs.trace,hc,(extract_eq _ _).symm.trans hw,fun k c hk tr => hs.prefix hk tr⟩

end DetDLP.EntryTapeCode
end

open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open BitProgram

theorem solution (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (Q : Program 3 s l) (it iv ot ov : Fin s), it≠iv ∧ ot≠ov ∧
    ∀ (input output : List Bool) (T M : ℝ),RunsWithin E out (true::input) output T M →
      ∀ r : Fin 3→Bool,
      let initial : Cfg 3 s l := ⟨some Q.entry,r,fun j =>
        if j=it then List.replicate input.length true else if j=iv then input else []⟩
      ∃ (n : ℕ) (final : Cfg 3 s l), (n:ℝ)≤8*T ∧ BitProgram.Trace Q n initial final ∧
        final.pc=none ∧ ((((final.stacks ot).zip (final.stacks ov)).takeWhile Prod.fst).map Prod.snd)=output ∧
        ∀ k c,k≤n→ BitProgram.Trace Q k initial c→∀ j,(c.stacks j).length≤⌊M⌋₊+8 := by
  exact EntryTapeCode.callback E out
