-- Prove2me | solution 1 for DetDLP.depth_first_contraction_control_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T17:36:34.594333+00:00
-- url     : https://prove2.me/submissions/0802404c-9856-41ab-9cc1-f262dd5f4341

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S067
import Definitions.Def_DetDLP_Machine

section
namespace DetDLP.BoundedProgramLoop
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking
/-- A time-indexed run annotated at every visited configuration. -/
inductive SafeTrace {S : Type} (step : S → Option S) (ok : S → Prop) : ℕ → S → S → Prop
  | refl (s : S) : ok s  →  SafeTrace step ok 0 s s
  | cons {s t u k} : ok s  →  step s=some t  →  SafeTrace step ok k t u  →  SafeTrace step ok (k+1) s u
namespace SafeTrace
variable {S T : Type} {f : S → Option S} {g : T → Option T} {P : S → Prop} {Q : T → Prop}
theorem forget {k s t} (tr : SafeTrace f P k s t) : Computation.Trace f k s t := by
  induction tr with
  | refl s _ => exact .refl _
  | cons _ hs _ ih => exact .cons hs ih
theorem trans {n m a b c} (tr : SafeTrace f P n a b) (u : SafeTrace f P m b c) : SafeTrace f P (n+m) a c := by
  induction tr with
  | refl => simpa using u
  | cons h hs _ ih => exact (Nat.succ_add _ _).symm ▸ SafeTrace.cons h hs (ih u)
theorem within {n s t} (tr : SafeTrace f P n s t) :
    ∀ j c,j≤n → Computation.Trace f j s c → P c := by
  induction tr with
  | refl _ h =>
    intro j c hj hp
    obtain rfl : j=0 := by omega
    cases hp; exact h
  | cons h step tail ih =>
    intro j c hj hp; cases hp with
    | refl => exact h
    | cons hs ht => obtain rfl := Option.some.inj (step.symm.trans hs); exact ih _ _ (by omega) ht
theorem of_trace {n s t} (tr : Computation.Trace f n s t)
    (cap : ∀ j c,j≤n → Computation.Trace f j s c → P c) : SafeTrace f P n s t := by
  induction tr with
  | refl => exact .refl _ (cap _ _ (by omega) (.refl _))
  | cons step tail ih =>
    exact .cons (cap _ _ (by omega) (.refl _)) step (ih (fun j c hj tr => cap _ c (by omega) (.cons step tr)))
theorem map {n a b} (tr : SafeTrace f P n a b) (E : S → T)
    (next : ∀ x y,f x=some y → g (E x)=some (E y)) (safe : ∀ x,P x → Q (E x)) : SafeTrace g Q n (E a) (E b) := by
  induction tr with
  | refl _ h => exact .refl _ (safe _ h)
  | cons h hs _ ih => exact .cons (safe _ h) (next _ _ hs) ih
end SafeTrace

variable {r s l : ℕ} (p : Program r s l) (flag : Fin r)
def head : Fin (2+l) := Fin.castAdd l 0
def donePc : Fin (2+l) := Fin.castAdd l 1
def address (i : Fin l) : Fin (2+l) := Fin.natAdd 2 i
def loop : Program r s (2+l) where
  inputStack := p.inputStack
  outputStack := p.outputStack
  entry := head
  code := Fin.addCases (fun i : Fin 2 => if i=0 then .branch flag headBody donePc else .halt)
    (fun i => relocateInstr id id address (some head) (p.code i))
where headBody := address p.entry

def cap {L : ℕ} (W : ℕ) (c : Cfg r s L) := ∀ i,(c.stacks i).length≤W
def embed (c : Cfg r s l) : Cfg r s (2+l) := ⟨relocatePc address (some head) c.pc,c.regs,c.stacks⟩
theorem block {n x y W} (tr : SafeTrace (step p) (cap W) n x y) :
    SafeTrace (step (loop p flag)) (cap W) n (embed x) (embed y) := by
  let frame : Cfg r s (2+l) := ⟨some head,x.regs,x.stacks⟩
  have eq (z : Cfg r s l) : embed z=embedCfg id id address (some head) frame z := by
    cases z; simp [embed,embedCfg,Function.extend_id]
  apply tr.map embed _ (fun _ h => h)
  intro u v h; rw [eq,eq]
  apply relocate_step p _ id id address (some head) frame Function.injective_id Function.injective_id _ h
  intro j; simp [loop,address]

theorem test (z : Cfg r s (2+l)) (hz : z.pc=some head) :
    step (loop p flag) z=some {z with pc:=some (if z.regs flag then address p.entry else donePc)} := by
  rw [step,hz]; simp [loop,head,loop.headBody,execInstr]

theorem halt (z : Cfg r s (2+l)) (hz : z.pc=some donePc) :
    step (loop p flag) z=some {z with pc:=none} := by
  rw [step,hz]; simp [loop,donePc,execInstr]

/-- A block is a complete callback trace. Only its maximum stack length is charged across calls. -/
theorem run {S : Type} (cost : S → ℕ) (next : S → S) (R : S → Fin r → Bool) (V : S → Fin s → List Bool)
    (W : ℕ) (s0 : S) (n : ℕ)
    (terminal : R (next^[n] s0) flag=false)
    (stored : ∀ j,j≤n → ∀ i,(V (next^[j] s0) i).length≤W)
    (blocks : ∀ j,j<n → let z := next^[j] s0
      R z flag=true ∧ SafeTrace (step p) (cap W) (cost z)
        ⟨some p.entry,R z,V z⟩ ⟨none,R (next z),V (next z)⟩) :
    let P := loop p flag
    let total := 2+n+∑ j∈Finset.range n,cost (next^[j] s0)
    SafeTrace (step P) (cap W) total ⟨some P.entry,R s0,V s0⟩ ⟨none,R (next^[n] s0),V (next^[n] s0)⟩ := by
  intro P total
  induction n generalizing s0 with
  | zero =>
    have endbit : R s0 flag=false := terminal
    have space := stored 0 (by omega)
    let z : Cfg r s (2+l) := ⟨some head,R s0,V s0⟩
    have go := test p flag z rfl
    simp only [z,endbit,cond_false] at go
    exact .cons space go (.cons space (halt p flag _ rfl) (.refl _ space))
  | succ n ih =>
    have start := blocks 0 (by omega)
    change R s0 flag=true ∧ _ at start
    have st := stored 0 (by omega)
    let z : Cfg r s (2+l) := ⟨some head,R s0,V s0⟩
    have go := test p flag z rfl
    simp only [z,start.1,cond_true] at go
    have consume := SafeTrace.cons (show cap W z from st) go (block p flag start.2)
    have rest := ih (next s0) (by simpa only [Function.iterate_succ_apply] using terminal)
      (fun j hj => by simpa only [Function.iterate_succ_apply] using stored (j+1) (by omega))
      (fun j hj => by simpa only [Function.iterate_succ_apply] using blocks (j+1) (by omega))
    have both := consume.trans rest
    change SafeTrace _ _ ((cost s0+1)+(2+n+∑ j∈Finset.range n,cost (next^[j] (next s0)))) _ _ at both
    simpa only [z,P,total,loop,Finset.sum_range_succ',Function.iterate_succ_apply,Function.iterate_zero_apply,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using both
end DetDLP.BoundedProgramLoop
end

section
namespace DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT BoundedProgramLoop
inductive State where
  | eval (frame reply : ℕ) (pending : List ℕ)
  | halt (value : ℕ)
def deliver (v : ℕ) : List ℕ → State
  | [] => .halt v
  | x::xs => .eval x v xs
def advance (F : ℕ → ℕ → Answer) : State → State
  | .halt v => .halt v
  | .eval x y stack =>
    match F x y with
    | .value v => deliver v stack
    | .call save child => .eval child 0 (save::stack)
def running : State → Bool
  | .halt _ => false
  | .eval .. => true
def tick (F : ℕ → ℕ → Answer) (s : State) : Option State := if running s then some (advance F s) else none
def bounded (B D : ℕ) : State → Prop
  | .halt v => v<B
  | .eval x y stack => x<B ∧ y<B ∧ stack.length≤D ∧ ∀ t∈stack,t<B

def validStack (B D : ℕ) (stack : List ℕ) := stack.length≤D ∧ ∀ t∈stack,t<B
theorem delivery {B D v : ℕ} {stack : List ℕ} (hv : v<B) (hd : validStack B D stack) :
    bounded B D (deliver v stack) := by
  cases stack with
  | nil => exact hv
  | cons z zs =>
    have sz := hd.1
    exact ⟨hd.2 z (by simp),hv,by simp only [List.length_cons] at sz; omega,fun t ht => hd.2 t (by simp [ht])⟩

theorem simulate {B : ℕ} {F : ℕ → ℕ → Answer} {x y v n h : ℕ} (proof : Computes F B x y v n h)
    (stack : List ℕ) (D : ℕ) (space : stack.length+h≤D) (small : ∀ t∈stack,t<B) :
    SafeTrace (tick F) (bounded B D) n (.eval x y stack) (deliver v stack) := by
  induction proof generalizing stack with
  | value hx hy hv result =>
    refine .cons ⟨hx,hy,by omega,small⟩ ?_ (.refl _ (delivery hv ⟨by omega,small⟩))
    simp [tick,running,advance,result]
  | @call x y save child val v n h m k hx hy hs call c rest ih ih' =>
    have hleft : stack.length+(h+1)≤D := (Nat.add_le_add_left (le_max_left _ _) _).trans space
    have hright : stack.length+k≤D := (Nat.add_le_add_left (le_max_right _ _) _).trans space
    have lead := ih (save::stack) (by simp only [List.length_cons]; omega)
      (fun t ht => (List.mem_cons.mp ht).elim (fun eq => eq ▸ hs) (small t))
    have tail := ih' stack hright small
    have both := lead.trans tail
    have first : tick F (.eval x y stack)=some (.eval child 0 (save::stack)) := by simp [tick,running,advance,call]
    have full := SafeTrace.cons (show bounded B D (.eval x y stack) from ⟨hx,hy,by omega,small⟩) first both
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using full

theorem outcome {B : ℕ} {F : ℕ → ℕ → Answer} {x y v n h : ℕ} (proof : Computes F B x y v n h) :
    let start := State.eval x y []
    (advance F)^[n] start=.halt v ∧
      (∀ j,j≤n → bounded B h ((advance F)^[j] start)) ∧
      (∀ j,j<n → running ((advance F)^[j] start)=true) := by
  intro start
  have sim := simulate proof [] h (by simp) (by simp)
  have tr (j : ℕ) (s : State) : Computation.Trace (fun t => some (advance F t)) j s ((advance F)^[j] s) := by
    induction j generalizing s with
    | zero => exact .refl _
    | succ j ih => exact .cons rfl (ih (advance F s))
  have total : SafeTrace (fun s => some (advance F s)) (bounded B h) n start (.halt v) :=
    sim.map id (fun u z ht => by simp only [tick] at ht; split at ht <;> simp_all) (fun _ hu => hu)
  have eq : (advance F)^[n] start=.halt v := Option.some.inj (((tr n start).iterate.symm).trans total.forget.iterate)
  have pre := fun j (hj : j≤n) => total.within j _ hj (tr j start)
  refine ⟨eq,pre,?_⟩
  have before {k : ℕ} {s z : State} (trace : SafeTrace (tick F) (bounded B h) k s z) :
      ∀ j,j<k → running ((advance F)^[j] s)=true := by
    induction trace with
    | refl => intro j hj; omega
    | @cons s u z k ok ht tail ih =>
      have active : running s=true := by
        cases eq : running s
        · simp [tick,eq] at ht
        · rfl
      have step : advance F s=u := by simpa [tick,active] using ht
      intro j hj
      cases j with
      | zero => exact active
      | succ j => rw [Function.iterate_succ_apply,step]; apply ih; omega
  exact before sim
end DetDLP.ContinuationSchedule
end

section

namespace DetDLP.BitNormalize
open OAI.Algorithms.SubexponentialSAT BitProgram

/-- Remove high-order padding from a little-endian integer on stack zero. -/
def program : Program 2 2 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .push 1 0 0,
    .pop 1 0 1 4, .branch 1 5 9, .branch 0 6 3, .push 0 0 7,
    .pop 1 0 1 8, .branch 1 6 9, .halt]

private def cf (pc : Option (Fin 10)) (r : Fin 2 → Bool) (x y : List Bool) : Cfg 2 2 10 :=
  ⟨pc,r,![x,y]⟩

private def regs (v p : Bool) : Fin 2 → Bool := ![v,p]

private theorem reg (r : Fin 2 → Bool) (o : Option Bool) :
    readRegs r 0 1 o = regs (o.getD false) o.isSome := by funext i; fin_cases i <;> simp [readRegs,regs]
private theorem u0 (x y z : List Bool) : Function.update ![x,y] (0 : Fin 2) z = ![z,y] := by
  funext i; fin_cases i <;> simp [Function.update_apply]
private theorem u1 (x y z : List Bool) : Function.update ![x,y] (1 : Fin 2) z = ![x,z] := by
  funext i; fin_cases i <;> simp [Function.update_apply]

private theorem reverse_phase (xs ys : List Bool) (r : Fin 2 → Bool) :
    Trace program (3*xs.length+2) (cf (some 0) r xs ys)
      (cf (some 3) (regs false false) [] (xs.reverse++ys)) := by
  induction xs generalizing r ys with
  | nil =>
    refine .cons (b := cf (some 1) (regs false false) [] ys) ?_ (.cons (by rfl) (.refl _))
    simp [step,execInstr,cf,program,reg,u0]
  | cons b xs ih =>
    rw [List.length_cons,show 3*(xs.length+1)+2=(3*xs.length+2)+1+1+1 by omega]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    refine .cons (b := cf (some 1) (regs b true) xs ys) ?_
      (.cons (b := cf (some 2) (regs b true) xs ys) (by rfl) (.cons ?_ (ih (b::ys) (regs b true))))
    · simp [step,execInstr,cf,program,reg,u0]
    · simp [step,execInstr,cf,program,regs,u1]

private theorem restore_phase (xs ys : List Bool) (r : Fin 2 → Bool) :
    Trace program (3*ys.length+3) (cf (some 7) r xs ys)
      (cf none (regs false false) (ys.reverse++xs) []) := by
  induction ys generalizing r xs with
  | nil =>
    refine .cons (b := cf (some 8) (regs false false) xs []) ?_ (.cons (b := cf (some 9) (regs false false) xs []) (by rfl) (.cons (by rfl) (.refl _)))
    simp [step,execInstr,cf,program,reg,u1]
  | cons b ys ih =>
    rw [List.length_cons,show 3*(ys.length+1)+3=(3*ys.length+3)+1+1+1 by omega]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    refine .cons (b := cf (some 8) (regs b true) xs ys) ?_
      (.cons (b := cf (some 6) (regs b true) xs ys) (by rfl) (.cons ?_ (ih (b::xs) (regs b true))))
    · simp [step,execInstr,cf,program,reg,u1]
    · simp [step,execInstr,cf,program,regs,u0]

private def dropZeros : List Bool → List Bool
  | [] => []
  | false::xs => dropZeros xs
  | true::xs => true::xs

private theorem strip_phase (ys : List Bool) (r : Fin 2 → Bool) :
    ∃ k ≤ 3*ys.length+5, Trace program k (cf (some 3) r [] ys)
      (cf none (regs false false) (dropZeros ys).reverse []) := by
  induction ys generalizing r with
  | nil =>
    refine ⟨3,by decide,.cons (b := cf (some 4) (regs false false) [] []) ?_
      (.cons (b := cf (some 9) (regs false false) [] []) (by rfl) (.cons (by rfl) (.refl _)))⟩
    simp [step,execInstr,cf,program,reg,u1]
  | cons b ys ih =>
    cases b with
    | false =>
      obtain ⟨k,hk,tr⟩ := ih (regs false true)
      refine ⟨k+3,by simp; omega,.cons (b := cf (some 4) (regs false true) [] ys) ?_
        (.cons (b := cf (some 5) (regs false true) [] ys) (by rfl) (.cons (by rfl) tr))⟩
      simp [step,execInstr,cf,program,reg,u1]
    | true =>
      have ht := restore_phase [true] ys (regs true true)
      rw [← List.reverse_cons] at ht
      refine ⟨3*ys.length+3+4,by simp; omega,.cons (b := cf (some 4) (regs true true) [] ys) ?_
        (.cons (b := cf (some 5) (regs true true) [] ys) (by rfl)
          (.cons (b := cf (some 6) (regs true true) [] ys) (by rfl) (.cons ?_ ht)))⟩
      · simp [step,execInstr,cf,program,reg,u1]
      · simp [step,execInstr,cf,program,regs,u0]

private theorem value_append_zero (xs : List Bool) : BinaryArithmetic.toNat (xs++[false]) = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]

private theorem canon_high (ys : List Bool) :
    (dropZeros ys).reverse = (BinaryArithmetic.toNat ys.reverse).bits := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys b ih =>
    rw [List.reverse_append,List.reverse_singleton,List.singleton_append]
    have hstep : BinaryArithmetic.toNat (b::ys.reverse) = Nat.bit b (BinaryArithmetic.toNat ys.reverse) := by
      cases b <;> simp [Nat.bit,BinaryArithmetic.toNat_cons] <;> omega
    rw [hstep]
    by_cases hy : dropZeros ys = []
    · have hz : BinaryArithmetic.toNat ys.reverse = 0 := by
        have hx := ih.symm; rw [hy] at hx
        have hl := congrArg List.length hx
        rw [Nat.size_eq_bits_len] at hl
        exact Nat.size_eq_zero.mp hl
      have ha : dropZeros (ys++[b]) = dropZeros [b] := by
        clear ih hz hstep
        induction ys with
        | nil => rfl
        | cons v ys ih =>
          cases v with
          | false => exact ih hy
          | true => simp [dropZeros] at hy
      rw [ha,hz]; cases b <;> decide
    · have hv : BinaryArithmetic.toNat ys.reverse ≠ 0 := by
        intro hz; rw [hz] at ih; simp_all
      have ha : dropZeros (ys++[b]) = dropZeros ys++[b] := by
        clear ih hv hstep
        induction ys with
        | nil => contradiction
        | cons v ys ih =>
          cases v with
          | false => exact ih hy
          | true => rfl
      rw [ha,List.reverse_append,List.reverse_singleton,List.singleton_append,ih,Nat.bits_append_bit _ _ (fun e => (hv e).elim)]

/-- Canonical output and a linear instruction bound for every word, including padded zero. -/
theorem normalizes (xs : List Bool) (r : Fin 2 → Bool) :
    ∃ k ≤ 6*xs.length+7, Trace program k (cf (some 0) r xs [])
      (cf none (regs false false) (BinaryArithmetic.toNat xs).bits []) := by
  have h := reverse_phase xs [] r; simp only [List.append_nil] at h
  obtain ⟨k,hk,hh⟩ := strip_phase xs.reverse (regs false false)
  rw [canon_high,List.reverse_reverse] at hh
  exact ⟨_,by simp only [List.length_reverse] at hk; omega,h.trans hh⟩

end DetDLP.BitNormalize
end

section

namespace DetDLP.BitNormalize
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking

private theorem cfg_eq {r s l : ℕ} {a b : Cfg r s l} (hp : a.pc=b.pc) (hr : a.regs=b.regs)
    (hs : a.stacks=b.stacks) : a=b := by cases a; cases b; simp_all

private def regMap : Fin 2 → Fin 8 := Fin.castAdd 6
private def ports (k t : Fin 8) : Fin 2 → Fin 8 := ![k,t]
private theorem ports_inj {k t : Fin 8} (h : k ≠ t) : Function.Injective (ports k t) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp_all [ports,Ne.symm h]

def atPort (k t : Fin 8) := liftProgram program regMap (ports k t)

theorem atPort_runs (k t : Fin 8) (hk : k ≠ t) (r : Fin 8 → Bool) (stk : Fin 8 → List Bool)
    (ht : stk t = []) :
    ∃ rf : Fin 8 → Bool, RunsIn (atPort k t) (6*(stk k).length+7)
      ⟨some 0,r,stk⟩ ⟨none,rf,Function.update stk k (BinaryArithmetic.toNat (stk k)).bits⟩ := by
  let frame : Cfg 8 8 10 := ⟨none,r,stk⟩
  have hr : Function.Injective regMap := Fin.castAdd_injective _ _
  have hs := ports_inj hk
  obtain ⟨n,hn,h⟩ := normalizes (stk k) (r ∘ regMap)
  change Trace program n ⟨some 0,r ∘ regMap,![stk k,[]]⟩
      ⟨none,![false,false],![(BinaryArithmetic.toNat (stk k)).bits,[]]⟩ at h
  have tr := liftProgram_trace program regMap (ports k t) frame hr hs h
  let start : Cfg 2 2 10 := ⟨some 0,r ∘ regMap,![stk k,[]]⟩
  let finish : Cfg 2 2 10 := ⟨none,![false,false],![(BinaryArithmetic.toNat (stk k)).bits,[]]⟩
  have e0 : embedCfg regMap (ports k t) id none frame start = ⟨some 0,r,stk⟩ := by
    refine cfg_eq rfl ?_ ?_
    · funext j
      by_cases hj : ∃ x,regMap x = j
      · obtain ⟨x,rfl⟩ := hj; exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ hj
    · funext j
      by_cases hj : ∃ x,ports k t x = j
      · obtain ⟨x,rfl⟩ := hj
        rw [embedCfg_stack _ _ _ _ _ _ hs]; fin_cases x <;> simp [ports,start,ht]
      · exact Function.extend_apply' _ _ _ hj
  let final := embedCfg regMap (ports k t) id none frame finish
  have e1 : final = ⟨none,final.regs,Function.update stk k (BinaryArithmetic.toNat (stk k)).bits⟩ := by
    refine cfg_eq rfl rfl ?_
    funext j
    by_cases hj : ∃ x, ports k t x = j
    · obtain ⟨x,rfl⟩ := hj
      dsimp only [final]
      rw [embedCfg_stack _ _ _ _ _ _ hs]
      fin_cases x <;> simp [ports,finish,Function.update_apply,hk,hk.symm,ht]
    · have hjk : j ≠ k := fun h => hj ⟨0,by simp [ports,h]⟩
      change final.stacks j = Function.update stk k (BinaryArithmetic.toNat (stk k)).bits j
      rw [Function.update_of_ne hjk]
      exact Function.extend_apply' _ _ _ hj
  refine ⟨final.regs,n,hn,?_⟩
  change Trace (atPort k t) n (embedCfg regMap (ports k t) id none frame start) final at tr
  rw [e0,e1] at tr
  exact tr

end DetDLP.BitNormalize
end

section

namespace DetDLP.BitEuclidDivision
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking ModularQuotientPrograms

private def cleanup := link (BitNormalize.atPort 0 1) (BitNormalize.atPort 7 1)
def divide := link quotientProgram cleanup

/-- Both results have canonical binary lengths before they are used by the next Euclidean iteration. -/
theorem divide_correct (regs : Fin 8 → Bool) (m x : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ rf, RunsIn divide (125*(m.length+x.length+1)^2)
        ⟨some 0,regs,quotientStacks [] m x []⟩
        ⟨none,rf,quotientStacks (BinaryArithmetic.toNat x % BinaryArithmetic.toNat m).bits m []
                  (BinaryArithmetic.toNat x / BinaryArithmetic.toNat m).bits⟩ := by
  obtain ⟨r1,q,b,hdiv,hq,hb,vq,vb⟩ := quotient_value regs m x hm
  let stk := quotientStacks b m [] q
  obtain ⟨r2,hbtr⟩ := BitNormalize.atPort_runs 0 1 (by decide) r1 stk rfl
  let b' := (BinaryArithmetic.toNat b).bits
  have e0 : Function.update stk 0 b' = quotientStacks b' m [] q := by
    funext i; fin_cases i <;> simp [stk,quotientStacks,Function.update_apply]
  change RunsIn (BitNormalize.atPort 0 1) (6*b.length+7)
      ⟨some 0,r1,stk⟩ ⟨none,r2,Function.update stk 0 b'⟩ at hbtr
  rw [e0] at hbtr
  obtain ⟨r3,hqtr⟩ := BitNormalize.atPort_runs 7 1 (by decide) r2 (quotientStacks b' m [] q) rfl
  let q' := (BinaryArithmetic.toNat q).bits
  have e7 : Function.update (quotientStacks b' m [] q) 7 q' = quotientStacks b' m [] q' := by
    funext i; fin_cases i <;> simp [quotientStacks,Function.update_apply]
  change RunsIn (BitNormalize.atPort 7 1) (6*q.length+7)
      ⟨some 0,r2,quotientStacks b' m [] q⟩ ⟨none,r3,Function.update (quotientStacks b' m [] q) 7 q'⟩ at hqtr
  rw [e7] at hqtr
  have hclean := link_runsIn _ _ hbtr rfl hqtr
  change RunsIn cleanup _ ⟨some 0,r1,stk⟩ ⟨none,r3,quotientStacks b' m [] q'⟩ at hclean
  have h := link_runsIn _ _ hdiv rfl hclean
  change RunsIn divide _ ⟨some 0,regs,quotientStacks [] m x []⟩ ⟨none,r3,quotientStacks b' m [] q'⟩ at h
  dsimp only [b',q'] at h; rw [vq,vb] at h
  refine ⟨r3,h.mono ?_⟩
  rw [hq,hb]; nlinarith only [Nat.zero_le m.length,Nat.zero_le x.length,Nat.zero_le (m.length*x.length),
    Nat.zero_le (x.length^2),Nat.zero_le (m.length^2)]
end DetDLP.BitEuclidDivision
end

section

namespace DetDLP.BoundedExtendedEuclid

/-- Two successive remainders and their signed coefficient rows. -/
structure State where
  r : ℕ
  u : ℤ
  v : ℤ
  oldR : ℕ
  oldU : ℤ
  oldV : ℤ
  deriving Repr

def step (s : State) : State :=
  if s.r = 0 then s else
    let q : ℤ := s.oldR/s.r
    ⟨s.oldR%s.r,s.oldU-q*s.u,s.oldV-q*s.v,s.r,s.u,s.v⟩

def run : ℕ → State → State
  | 0,s => s
  | k+1,s => run k (step s)

private def result (s : State) := Nat.xgcdAux s.r s.u s.v s.oldR s.oldU s.oldV

private theorem step_result (s : State) : result (step s) = result s := by
  by_cases hr : s.r = 0
  · simp [step,hr]
  · simp only [result,step,if_neg hr]
    exact (Nat.xgcdAux_rec (Nat.pos_of_ne_zero hr)).symm

private theorem run_result (k : ℕ) (s : State) : result (run k s) = result s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact (ih (step s)).trans (step_result s)

private theorem mod_twice (a b : ℕ) (h : 0 < b) (hle : b ≤ a) : 2*(a%b) ≤ a := by
  by_cases half : 2*b ≤ a
  · have := Nat.mod_lt a h; omega
  · rw [Nat.mod_eq_sub_mod hle,Nat.mod_eq_of_lt (by omega : a-b < b)]; omega

private theorem shrink (s : State) : 2*(step (step s)).r ≤ s.r := by
  by_cases h : s.r = 0
  · simp [step,h]
  · have hg : (step s).r = s.oldR%s.r := by simp [step,h]
    have ho : (step s).oldR = s.r := by simp [step,h]
    by_cases hz : (step s).r = 0
    · have eqs : step (step s) = step s := if_pos hz
      rw [eqs,hz]; simp
    · have ht : (step s).r < s.r := by rw [hg]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
      calc
        _ = 2*(s.r % (step s).r) := by have hg2 : (step (step s)).r = (step s).oldR % (step s).r := congrArg State.r (if_neg hz : step (step s) = _)
                                       rw [hg2,ho]
        _ ≤ _ := mod_twice _ _ (Nat.pos_of_ne_zero hz) ht.le

private theorem stopped (h : ℕ) (s : State) (hs : s.r < 2^h) : (run (2*h) s).r = 0 := by
  induction h generalizing s with
  | zero => simp [run] at *; omega
  | succ h ih =>
    rw [Nat.mul_succ]
    change (run (2*h) (step (step s))).r = 0
    apply ih
    have := shrink s; rw [pow_succ] at hs; omega

private def Bounded (M A : ℕ) (s : State) :=
  s.r ≤ M ∧ s.oldR ≤ M ∧ s.u.natAbs ≤ A ∧ s.v.natAbs ≤ A ∧ s.oldU.natAbs ≤ A ∧ s.oldV.natAbs ≤ A

private theorem bound_step {M A : ℕ} {s : State} (h : Bounded M A s) : Bounded M ((M+1)*A) (step s) := by
  obtain ⟨hr,ho,hu,hv,hou,hov⟩ := h
  have ha : A ≤ (M+1)*A := by rw [Nat.add_mul]; omega
  by_cases hz : s.r = 0
  · simp only [step,if_pos hz,Bounded]; omega
  · have hq : s.oldR/s.r ≤ M := (Nat.div_le_self ..).trans ho
    have hcomb (x y : ℤ) (hx : x.natAbs ≤ A) (hy : y.natAbs ≤ A) :
        (x-((s.oldR/s.r : ℕ):ℤ)*y).natAbs ≤ (M+1)*A := by
      apply (Int.natAbs_sub_le ..).trans
      rw [Int.natAbs_mul,Int.natAbs_natCast,Nat.add_mul,one_mul]
      exact (Nat.add_le_add hx (Nat.mul_le_mul hq hy)).trans_eq (add_comm ..)
    simp only [step,if_neg hz,Bounded]
    exact ⟨(Nat.mod_le ..).trans ho,hr,hcomb _ _ hou hu,hcomb _ _ hov hv,hu.trans ha,hv.trans ha⟩

private theorem bound_run (k M A : ℕ) (s : State) (h : Bounded M A s) :
    Bounded M ((M+1)^k*A) (run k s) := by
  induction k generalizing s A with
  | zero => simpa [run] using h
  | succ k ih => simpa [run,pow_succ,mul_assoc] using ih ((M+1)*A) (step s) (bound_step h)

def init (x y : ℕ) : State := ⟨x,1,0,y,0,1⟩

/-- A logarithmic, input-independent iteration cap suffices for the exact coefficients
used in the column program. The polynomial bit bound covers every prefix, even before stopping. -/
theorem costed_xgcd {M : ℕ} (x y : ℕ) (hx : x ≤ M) (hy : y ≤ M) :
    let h := bitLen M+1
    let z := run (2*h) (init x y)
    z.r = 0 ∧ z.oldR = x.gcd y ∧ z.oldU = x.gcdA y ∧ z.oldV = x.gcdB y ∧
      ∀ k ≤ 2*h, let s := run k (init x y)
        s.r ≤ M ∧ s.oldR ≤ M ∧
          ∀ a ∈ [s.u,s.v,s.oldU,s.oldV], a.natAbs ≤ 2^(2*h^2) := by
  intro h z
  have hM := Nat.le_pow_clog (b := 2) (by decide) M
  have hh : M+1 ≤ 2^h := by
    dsimp [h,bitLen]; rw [pow_succ]
    have hp : 0 < 2^Nat.clog 2 M := by positivity
    omega
  have hz : z.r = 0 := stopped h _ (by change x < 2^h; omega)
  have he := run_result (2*h) (init x y)
  change Nat.xgcdAux z.r z.u z.v z.oldR z.oldU z.oldV = Nat.xgcdAux x 1 0 y 0 1 at he
  rw [hz,Nat.xgcd_zero_left] at he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg (fun z => z.2.1) he
  have h3 := congrArg (fun z => z.2.2) he
  refine ⟨hz,h1.trans (Nat.xgcdAux_fst ..),h2,h3,?_⟩
  intro k hk s
  have hh0 : Bounded M 1 (init x y) := by simp [Bounded,init,hx,hy]
  obtain ⟨hr,ho,h1,h2,h3,h4⟩ := bound_run k M 1 _ hh0
  have hab : (M+1)^k*1 ≤ 2^(2*h^2) := by
    rw [mul_one]
    calc
      _ ≤ (2^h)^k := Nat.pow_le_pow_left hh _
      _ = 2^(h*k) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left h hk])
  refine ⟨hr,ho,?_⟩
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> first | exact h1.trans hab | exact h2.trans hab | exact h3.trans hab | exact h4.trans hab
end DetDLP.BoundedExtendedEuclid
end

section

namespace DetDLP.BitEuclidLoop
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls ModularQuotientPrograms
open StackRoutines

abbrev Code := Cmd 8 8
abbrev Data := State 8 8
abbrev regs := Fin 8 → Bool
abbrev Stk := Fin 8 → List Bool

theorem nat_bits (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h,BinaryArithmetic.toNat_cons,ih]
    cases b <;> simp [Nat.bit] <;> omega

private abbrev transfer (src dst : Fin 8) : Code := .call (transferProgram src dst 0 1)
private def move (src dst : Fin 8) : Code := .seq (transfer src 1) (transfer 1 dst)

private theorem move_eval (src dst : Fin 8) (hs : src ≠ 1) (hd : dst ≠ 1) (hsd : src ≠ dst)
    (r : regs) (st : Stk) (ht : st 1 = []) (he : st dst = []) :
    ∃ rf, Eval (move src dst) (6*(st src).length+6)
      ⟨r,st⟩ ⟨rf, Function.update (Function.update st src []) dst (st src)⟩ := by
  have h₁ := ArrayUpdatePrograms.transfer_eval src 1 0 1 hs (by decide) r st
  have h₂ := ArrayUpdatePrograms.transfer_eval 1 dst 0 1 (Ne.symm hd) (by decide)
    (readRegs r 0 1 none) (transferStacks src 1 st)
  have h := Eval.seq h₁ h₂
  have heq : transferStacks 1 dst (transferStacks src 1 st) =
      Function.update (Function.update st src []) dst (st src) := by
    funext i
    by_cases h1 : i = 1
    · subst i; simp [transferStacks,Function.update_apply,hs,hd,Ne.symm hs,Ne.symm hd,ht]
    · by_cases h2 : i = dst
      · subst i; simp [transferStacks,Function.update_apply,hs,hd,hsd,Ne.symm hs,Ne.symm hsd,ht,he]
      · simp [transferStacks,Function.update_apply,h1,h2]
  rw [heq] at h
  refine ⟨readRegs (readRegs r 0 1 none) 0 1 none,?_⟩
  have eqn : 3*(st src).length+3+(3*(transferStacks src 1 st 1).length+3) = 6*(st src).length+6 := by
    simp [transferStacks,ht]; omega
  rw [eqn] at h
  exact h

private def peek : Code := .base (.atom (.peek 5 0 1))
private abbrev peekR (r : regs) (w : List Bool) := readRegs r 0 1 w.head?
private theorem peek_eval (r : regs) (st : Stk) :
    Eval peek 1 ⟨r,st⟩ ⟨peekR r (st 5),st⟩ :=
  .base (.atom _ _)

private def body : Code := .seq (.call BitEuclidDivision.divide)
  (.seq (ArithmeticExpressionSupport.clearCmd 7)
    (.seq (move 5 6) (.seq (move 0 5) peek)))
def code : Code := .seq peek (.while 1 body)

private abbrev store (d x : ℕ) : Stk := quotientStacks [] d.bits x.bits []

private theorem guard (r : regs) (d : ℕ) :
    peekR r d.bits 1 = decide (d ≠ 0) := by
  simp only [peekR,readRegs,Function.update_self]
  cases hw : d.bits with
  | nil =>
    have h : d = 0 := Nat.size_eq_zero.mp (by rw [← Nat.size_eq_bits_len,hw]; rfl)
    simp [h]
  | cons b bs =>
    have h : d ≠ 0 := fun e => by simp [e] at hw
    simp [h]

private theorem body_eval (r : regs) (d x M : ℕ) (hp : 0 < d)
    (hd : d ≤ M) (hx : x ≤ M) :
    ∃ n rf, n ≤ 600*(M.size+1)^2 ∧
      Eval body n ⟨r,store d x⟩ ⟨rf,store (x%d) d⟩ ∧ rf 1 = decide (x%d ≠ 0) := by
  have hp' : 0 < BinaryArithmetic.toNat d.bits := by rwa [nat_bits]
  obtain ⟨r₁,n,hn,ht⟩ := BitEuclidDivision.divide_correct r d.bits x.bits hp'
  simp only [nat_bits] at ht
  let a := (x%d).bits
  let b := (x/d).bits
  have e₁ : Eval (.call BitEuclidDivision.divide) n ⟨r,store d x⟩ ⟨r₁,quotientStacks a d.bits [] b⟩ := .call _ ht
  have e₂ := ArithmeticExpressionSupport.clear_eval 7 (⟨r₁,quotientStacks a d.bits [] b⟩ : Data)
  have eq₂ : Function.update (quotientStacks a d.bits [] b) 7 [] = quotientStacks a d.bits [] [] := by
    funext i; fin_cases i <;> rfl
  rw [eq₂] at e₂
  obtain ⟨r₃,e₃⟩ := move_eval 5 6 (by decide) (by decide) (by decide)
    (readRegs r₁ 0 1 none) (quotientStacks a d.bits [] []) rfl rfl
  have eq₃ : Function.update (Function.update (quotientStacks a d.bits [] []) 5 []) 6 d.bits =
      quotientStacks a [] d.bits [] := by funext i; fin_cases i <;> rfl
  change Eval _ (6*d.bits.length+6) _ ⟨r₃,Function.update (Function.update _ 5 []) 6 d.bits⟩ at e₃
  rw [eq₃] at e₃
  obtain ⟨r₄,e₄⟩ := move_eval 0 5 (by decide) (by decide) (by decide) r₃ (quotientStacks a [] d.bits []) rfl rfl
  have eq₄ : Function.update (Function.update (quotientStacks a [] d.bits []) 0 []) 5 a =
      store (x%d) d := by funext i; fin_cases i <;> rfl
  change Eval _ (6*a.length+6) _ ⟨r₄,Function.update (Function.update _ 0 []) 5 a⟩ at e₄
  rw [eq₄] at e₄
  have ht := Eval.seq e₁ (Eval.seq e₂ (Eval.seq e₃ (Eval.seq e₄ (peek_eval r₄ (store (x%d) d)))))
  refine ⟨_,_,?_,ht,guard _ _⟩
  change n+(2*b.length+3+(6*d.bits.length+6+(6*a.length+6+1))) ≤ _
  dsimp only [a,b]
  simp only [Nat.size_eq_bits_len] at hn ⊢
  have hd' := Nat.size_le_size hd
  have hx' := Nat.size_le_size hx
  have hr := Nat.size_le_size ((Nat.mod_le x d).trans hx)
  have hq := Nat.size_le_size ((Nat.div_le_self x d).trans hx)
  have hsq := Nat.pow_le_pow_left (show d.size+x.size+1 ≤ 2*(M.size+1) by omega) 2
  nlinarith only [hn,hsq,hr,hq,hd',hx',Nat.zero_le (M.size^2),Nat.zero_le M.size]

open BoundedExtendedEuclid in
private theorem run_zero (k : ℕ) (s : BoundedExtendedEuclid.State) (hz : s.r=0) : run k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [run,BoundedExtendedEuclid.step,hz] using ih

open BoundedExtendedEuclid in
private theorem loop_eval (k M : ℕ) (s : BoundedExtendedEuclid.State)
    (r : regs) (hr : s.r ≤ M) (hx : s.oldR ≤ M) (hg : r 1 = decide (s.r ≠ 0))
    (hstop : (run k s).r = 0) :
    ∃ n rf, n ≤ k*(600*(M.size+1)^2+1)+1 ∧
      Eval (.while 1 body) n ⟨r,store s.r s.oldR⟩ ⟨rf,store 0 (run k s).oldR⟩ := by
  by_cases hz : s.r = 0
  · refine ⟨1,r,by omega,?_⟩
    rw [run_zero k s hz, hz]
    exact .while_false (by simpa [hz] using hg)
  induction k generalizing s r with
  | zero => exact False.elim (hz hstop)
  | succ k ih =>
    obtain ⟨n₁,r₁,hn₁,he₁,hg₁⟩ := body_eval r s.r s.oldR M (Nat.pos_of_ne_zero hz) hr hx
    have hs : (step s).r = s.oldR%s.r := by simp [BoundedExtendedEuclid.step,hz]
    have ho : (step s).oldR = s.r := by simp [BoundedExtendedEuclid.step,hz]
    have hrem := (Nat.mod_le s.oldR s.r).trans hx
    have hnext : ∃ n rf, n ≤ k*(600*(M.size+1)^2+1)+1 ∧
        Eval (.while 1 body) n ⟨r₁,store (step s).r (step s).oldR⟩
          ⟨rf,store 0 (run k (step s)).oldR⟩ := by
      by_cases hnew : (step s).r = 0
      · refine ⟨1,r₁,by omega,?_⟩
        rw [run_zero k _ hnew,hnew]
        exact .while_false (by simpa [← hs,hnew] using hg₁)
      · exact ih (step s) r₁ (hs ▸ hrem) (ho ▸ hr) (hs ▸ hg₁) hstop hnew
    obtain ⟨n₂,rf,hn₂,he₂⟩ := hnext
    rw [hs,ho] at he₂
    refine ⟨_,rf,?_,.while_true (by simpa [hz] using hg) he₁ he₂⟩
    rw [Nat.succ_mul]; omega

/-- Fixed eight-stack GCD table, including the zero case. Every division returns
canonical words before the next guard is tested. -/
def program := compiled code 5 6

theorem gcd_trace (r : regs) (d x : ℕ) :
    ∃ rf, RunsIn program (2*(bitLen (max d x)+1)*(600*((max d x).size+1)^2+1)+3)
      ⟨some program.entry,r,store d x⟩ ⟨none,rf,store 0 (d.gcd x)⟩ := by
  let M := max d x
  let k := 2*(bitLen M+1)
  obtain ⟨hz,hg,-⟩ := BoundedExtendedEuclid.costed_xgcd d x (le_max_left d x) (le_max_right d x)
  have h := loop_eval k M (BoundedExtendedEuclid.init d x) (peekR r d.bits)
    (le_max_left d x) (le_max_right d x) (guard r d) hz
  obtain ⟨n,rf,hn,he⟩ := h
  rw [hg] at he
  have hfull := compiled_halt_trace (Eval.seq (peek_eval r (store d x)) he) 5 6
  refine ⟨rf,_,?_,hfull⟩
  dsimp [k,M] at hn
  omega
end DetDLP.BitEuclidLoop
end

section

namespace DetDLP.BitArithmeticUnit
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls ModularQuotientPrograms
open ArithmeticExpressionSupport
abbrev Code := Cmd 8 8
abbrev Data := State 8 8
abbrev Regs := Fin 8 → Bool

inductive Op where | add | mul | quot | rem
  deriving DecidableEq, Repr

def Op.eval : Op → ℕ → ℕ → ℕ
  | .add,m,x => m+x
  | .mul,m,x => m*x
  | .quot,m,x => x/m
  | .rem,m,x => x%m

def Op.Valid (op : Op) (m : ℕ) := (op = .quot ∨ op = .rem) → 0 < m

private def ports : ArithmeticCalls.Ports 8 where
  left := 5
  right := 6
  out := 7
  work := ⟨Fin.castAdd 3,Fin.castAdd_injective 5 3⟩
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by decide
  work_ne_right := by decide
  work_ne_out := by decide

private def normalize : Code := .call (BitNormalize.atPort 7 1)
private def posop (op : Bool) : Code := .seq
  (if op then ArithmeticCalls.multiplyAt ports else ArithmeticCalls.addAt ports)
  (.seq (clearCmd 5) (.seq (clearCmd 6) normalize))

private theorem posop_correct (op : Bool) (r : Regs) (m x : ℕ) :
    ∃ n rf, n ≤ 160*(m.size+x.size+1)^2 ∧
      Eval (posop op) n ⟨r,quotientStacks [] m.bits x.bits []⟩
        ⟨rf,quotientStacks [] [] [] (if op then m*x else m+x).bits⟩ := by
  let d : Data := ⟨r,quotientStacks [] m.bits x.bits []⟩
  have hv : ArithmeticCalls.Valid ports d := ⟨rfl,by intro i; fin_cases i <;> rfl⟩
  have he : ∃ t rf word,
      Eval (if op then ArithmeticCalls.multiplyAt ports else ArithmeticCalls.addAt ports) t d
        ⟨rf,Function.update d.stacks ports.out word⟩ ∧
      BinaryArithmetic.toNat word = (if op then m*x else m+x) ∧
      word.length ≤ m.bits.length+x.bits.length+1 ∧ t ≤ 100*(m.bits.length+x.bits.length+1)^2 := by
    cases op
    · simpa [d,ports,BitEuclidLoop.nat_bits] using ArithmeticCalls.addAt_eval ports d hv
    · simpa [d,ports,BitEuclidLoop.nat_bits] using ArithmeticCalls.multiplyAt_eval ports d hv
  obtain ⟨n,r₁,w,he,hw,hl,hn⟩ := he
  have e1 : Function.update d.stacks ports.out w = quotientStacks [] m.bits x.bits w := by funext i; fin_cases i <;> rfl
  rw [e1] at he
  have h₂ := clear_eval 5 (⟨r₁,quotientStacks [] m.bits x.bits w⟩ : Data)
  have e2 : Function.update (quotientStacks [] m.bits x.bits w) 5 [] = quotientStacks [] [] x.bits w := by funext i; fin_cases i <;> rfl
  rw [e2] at h₂
  have h₃ := clear_eval 6 (⟨readRegs r₁ 0 1 none,quotientStacks [] [] x.bits w⟩ : Data)
  have e3 : Function.update (quotientStacks [] [] x.bits w) 6 [] = quotientStacks [] [] [] w := by funext i; fin_cases i <;> rfl
  rw [e3] at h₃
  obtain ⟨r₄,k,hk,ht⟩ := BitNormalize.atPort_runs 7 1 (by decide)
    (readRegs (readRegs r₁ 0 1 none) 0 1 none) (quotientStacks [] [] [] w) rfl
  change Trace _ k _ ⟨none,r₄,Function.update (quotientStacks [] [] [] w) 7 (BinaryArithmetic.toNat w).bits⟩ at ht
  have e4 : Function.update (quotientStacks [] [] [] w) 7 (BinaryArithmetic.toNat w).bits =
      quotientStacks [] [] [] (if op then m*x else m+x).bits := by rw [hw]; funext i; fin_cases i <;> rfl
  rw [e4] at ht
  have ht' : Eval normalize k ⟨_,quotientStacks [] [] [] w⟩ ⟨r₄,quotientStacks [] [] [] (if op then m*x else m+x).bits⟩ := .call _ ht
  refine ⟨_,_,?_,.seq he (.seq h₂ (.seq h₃ ht'))⟩
  change n+(2*m.bits.length+3+(2*x.bits.length+3+k)) ≤ _
  change k ≤ 6*w.length+7 at hk
  simp only [Nat.size_eq_bits_len] at hn hl ⊢
  nlinarith only [hn,hl,hk,Nat.zero_le (m.size^2),Nat.zero_le (x.size^2),Nat.zero_le (m.size*x.size),Nat.zero_le m.size,Nat.zero_le x.size]

private def divop (remainder : Bool) : Code :=
  .seq (.call BitEuclidDivision.divide) (.seq (clearCmd 5)
    (if remainder then .seq (clearCmd 7) (ArithmeticCalls.copyAt 0 7 1) else clearCmd 0))

private def divClean (remainder : Bool) : Code := .seq (divop remainder) (clearCmd 0)

private theorem divop_correct (rem : Bool) (r : Regs) (m x : ℕ) (hm : 0 < m) :
    ∃ n rf, n ≤ 160*(m.size+x.size+1)^2 ∧
      Eval (divClean rem) n ⟨r,quotientStacks [] m.bits x.bits []⟩
        ⟨rf,quotientStacks [] [] [] (if rem then x%m else x/m).bits⟩ := by
  obtain ⟨r₁,n,hn,ht⟩ := BitEuclidDivision.divide_correct r m.bits x.bits (by simpa [BitEuclidLoop.nat_bits] using hm)
  simp only [BitEuclidLoop.nat_bits] at ht
  let a := (x%m).bits
  let b := (x/m).bits
  have hd : Eval (.call BitEuclidDivision.divide) n ⟨r,quotientStacks [] m.bits x.bits []⟩ ⟨r₁,quotientStacks a m.bits [] b⟩ := .call _ ht
  have hc := clear_eval 5 (⟨r₁,quotientStacks a m.bits [] b⟩ : Data)
  have e : Function.update (quotientStacks a m.bits [] b) 5 [] = quotientStacks a [] [] b := by funext i; fin_cases i <;> rfl
  rw [e] at hc
  let r₂ := readRegs r₁ 0 1 none
  have ha : a.length ≤ x.size := by dsimp [a]; rw [Nat.size_eq_bits_len]; exact Nat.size_le_size (Nat.mod_le ..)
  have hb : b.length ≤ x.size := by dsimp [b]; rw [Nat.size_eq_bits_len]; exact Nat.size_le_size (Nat.div_le_self ..)
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len] at hn
  cases rem with
  | false =>
    have h₃ := clear_eval 0 (⟨r₂,quotientStacks a [] [] b⟩ : Data)
    have e₃ : Function.update (quotientStacks a [] [] b) 0 [] = quotientStacks [] [] [] b := by funext i; fin_cases i <;> rfl
    rw [e₃] at h₃
    have h₄ := clear_eval 0 (⟨readRegs r₂ 0 1 none,quotientStacks [] [] [] b⟩ : Data)
    rw [show Function.update (quotientStacks [] [] [] b) 0 [] = quotientStacks [] [] [] b by funext i; fin_cases i <;> rfl] at h₄
    refine ⟨_,_,?_,.seq (.seq hd (.seq hc h₃)) h₄⟩
    change n+(2*m.bits.length+3+(2*a.length+3))+3 ≤ _
    rw [Nat.size_eq_bits_len]
    nlinarith only [hn,ha,Nat.zero_le (m.size^2),Nat.zero_le (x.size^2),Nat.zero_le (m.size*x.size),Nat.zero_le m.size,Nat.zero_le x.size]
  | true =>
    have h₃ := clear_eval 7 (⟨r₂,quotientStacks a [] [] b⟩ : Data)
    have e₃ : Function.update (quotientStacks a [] [] b) 7 [] = quotientStacks a [] [] [] := by funext i; fin_cases i <;> rfl
    rw [e₃] at h₃
    have h₄ := ArithmeticCalls.copyAt_eval 0 7 1 (⟨readRegs r₂ 0 1 none,quotientStacks a [] [] []⟩ : Data)
      (by decide) (by decide) (by decide) rfl rfl
    have e₄ : Function.update (quotientStacks a [] [] []) 7 a = quotientStacks a [] [] a := by funext i; fin_cases i <;> rfl
    change Eval _ (7*a.length+5) _ ⟨_,Function.update (quotientStacks a [] [] []) 7 a⟩ at h₄
    rw [e₄] at h₄
    have h₅ := clear_eval 0 (⟨readRegs (readRegs r₂ 0 1 none) 0 1 none,quotientStacks a [] [] a⟩ : Data)
    rw [show Function.update (quotientStacks a [] [] a) 0 [] = quotientStacks [] [] [] a by funext i; fin_cases i <;> rfl] at h₅
    refine ⟨_,_,?_,.seq (.seq hd (.seq hc (.seq h₃ h₄))) h₅⟩
    change n+(2*m.bits.length+3+(2*b.length+3+(7*a.length+5)))+(2*a.length+3) ≤ _
    rw [Nat.size_eq_bits_len]
    nlinarith only [hn,ha,hb,Nat.zero_le (m.size^2),Nat.zero_le (x.size^2),Nat.zero_le (m.size*x.size),Nat.zero_le m.size,Nat.zero_le x.size]

def code : Op → Code
  | .add => posop false
  | .mul => posop true
  | .quot => divClean false
  | .rem => divClean true

theorem correct (op : Op) (r : Regs) (m x : ℕ) (hv : op.Valid m) :
    ∃ n rf, n ≤ 160*(m.size+x.size+1)^2 ∧
      Eval (code op) n ⟨r,quotientStacks [] m.bits x.bits []⟩ ⟨rf,quotientStacks [] [] [] (op.eval m x).bits⟩ := by
  cases op with
  | add => exact posop_correct false r m x
  | mul => exact posop_correct true r m x
  | quot => exact divop_correct false r m x (hv (Or.inl rfl))
  | rem => exact divop_correct true r m x (hv (Or.inr rfl))
end DetDLP.BitArithmeticUnit
end

section
namespace DetDLP.BitRegisterBank
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls ModularQuotientPrograms
open ArithmeticExpressionSupport BitArithmeticUnit

abbrev Vars (n : ℕ) := Fin n → ℕ
abbrev S (n : ℕ) := Fin (8+n)
abbrev Code (n : ℕ) := Cmd 8 (8+n)
abbrev low {n : ℕ} (i : Fin 8) : S n := Fin.castAdd n i
abbrev port {n : ℕ} (i : Fin n) : S n := Fin.natAdd 8 i

theorem low_ne_port {n : ℕ} (i : Fin 8) (j : Fin n) : low i ≠ port j := by
  intro he; have hh := congrArg Fin.val he
  change i.val = 8+j.val at hh; omega
def store {n : ℕ} (work : Fin 8 → List Bool) (v : Vars n) : S n → List Bool :=
  Fin.addCases work (fun j => (v j).bits)
@[simp] theorem store_low {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin 8) :
    store w v (low i) = w i := Fin.addCases_left ..
@[simp] theorem store_port {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin n) :
    store w v (port i) = (v i).bits := Fin.addCases_right ..

private theorem upd_low {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin 8) (xs : List Bool) :
    Function.update (store w v) (low i) xs = store (Function.update w i xs) v := by
  funext j; refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · change Function.update (store w v) (low i) xs (low l) = store _ _ (low l)
    simp [Function.update_apply,apply_ite,Fin.castAdd_inj]
    split <;> simp_all
  · change Function.update (store w v) (low i) xs (port l) = store _ _ (port l)
    simp [Function.update_of_ne (low_ne_port i l).symm]
private theorem upd_port {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin n) (x : ℕ) :
    Function.update (store w v) (port i) x.bits = store w (Function.update v i x) := by
  funext j; refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · change Function.update (store w v) (port i) x.bits (low l) = store _ _ (low l)
    simp [Function.update_of_ne (low_ne_port l i)]
  · change Function.update (store w v) (port i) x.bits (port l) = store _ _ (port l)
    by_cases hl : l=i
    · subst l; simp
    · have he : port l ≠ port i := fun h => hl (Fin.natAdd_injective _ _ h)
      simp [Function.update_of_ne he,Function.update_of_ne hl]

private def alu {n : ℕ} (op : Op) : Code n :=
  .call (ProgramLinking.liftProgram (compiled (BitArithmeticUnit.code op) 5 7) id low)
private def empty : Fin 8 → List Bool := fun _ => []

def assign {n : ℕ} (op : Op) (a b dst : Fin n) : Code n :=
  .seq (ArithmeticCalls.copyAt (port a) (low 5) (low 1))
    (.seq (ArithmeticCalls.copyAt (port b) (low 6) (low 1))
      (.seq (alu op) (.seq (clearCmd (port dst))
        (.seq (ArithmeticCalls.copyAt (low 7) (port dst) (low 1)) (clearCmd (low 7))))))

private theorem alu_eval {n : ℕ} (op : Op) (r : Regs) (a b : ℕ) (v : Vars n) (hv : op.Valid a) :
    ∃ t rf, t ≤ 160*(a.size+b.size+1)^2+1 ∧
      Eval (alu op) t ⟨r,store (quotientStacks [] a.bits b.bits []) v⟩
        ⟨rf,store (quotientStacks [] [] [] (op.eval a b).bits) v⟩ := by
  obtain ⟨t,rf,ht,he⟩ := BitArithmeticUnit.correct op r a b hv
  let frame : State 8 (8+n) := ⟨r,store empty v⟩
  have hh := eval_call_lifted _ id (@low n) frame Function.injective_id (Fin.castAdd_injective 8 n)
    (compiled_halt_trace he 5 7)
  have hframe (r' : Regs) (w : Fin 8 → List Bool) :
      embedState id (@low n) frame ⟨r',w⟩ = ⟨r',store w v⟩ := by
    apply embedState_eq_of_ports id _ frame _ _ Function.injective_id (Fin.castAdd_injective 8 n)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; simp
    · intro j; refine Fin.addCases (fun i hi => (hi ⟨i,rfl⟩).elim) (fun i _ => ?_) j
      change store w v (port i) = store empty v (port i); simp
  rw [hframe,hframe] at hh
  exact ⟨_,rf,by omega,hh⟩
private theorem copyIn {n} (w : Fin 8 → List Bool) (v : Vars n) (a : Fin n) (i : Fin 8)
    (hn : i ≠ 1) (hw : w i = []) (ht : w 1 = []) (r : Regs) :
    ∃ rf, Eval (ArithmeticCalls.copyAt (port a) (low i) (low 1)) (7*(v a).bits.length+5)
      ⟨r,store w v⟩ ⟨rf,store (Function.update w i (v a).bits) v⟩ := by
  have hi : (@low n 1) ≠ low i := fun h => hn (Fin.castAdd_injective 8 n h.symm)
  have hh := ArithmeticCalls.copyAt_eval (port a) (low i) (low 1) (⟨r,store w v⟩ : State 8 (8+n))
    (low_ne_port i a).symm (low_ne_port 1 a).symm hi (by simpa using hw) (by simpa using ht)
  refine ⟨readRegs r 0 1 none,?_⟩
  simpa [ArithmeticCalls.afterCopy,upd_low] using hh

theorem assign_eval {n : ℕ} (op : Op) (a b dst : Fin n) (v : Vars n) (r : Regs)
    (hv : op.Valid (v a)) :
    let y := op.eval (v a) (v b)
    ∃ t rf, t ≤ 160*((v a).size+(v b).size+1)^2 +
        10*((v a).size+(v b).size+(v dst).size+y.size+4) ∧
      Eval (assign op a b dst) t ⟨r,store empty v⟩ ⟨rf,store empty (Function.update v dst y)⟩ := by
  intro y
  obtain ⟨r₁,e₁⟩ := copyIn empty v a 5 (by decide) rfl rfl r
  have hw1 : Function.update empty 5 (v a).bits = quotientStacks [] (v a).bits [] [] := by
    funext i; fin_cases i <;> rfl
  rw [hw1] at e₁
  obtain ⟨r₂,e₂⟩ := copyIn (quotientStacks [] (v a).bits [] []) v b 6 (by decide) rfl rfl r₁
  have hw2 : Function.update (quotientStacks [] (v a).bits [] []) 6 (v b).bits =
      quotientStacks [] (v a).bits (v b).bits [] := by funext i; fin_cases i <;> rfl
  rw [hw2] at e₂
  obtain ⟨t,r₃,ht,e₃⟩ := alu_eval op r₂ (v a) (v b) v hv
  let w := quotientStacks [] [] [] y.bits
  change Eval _ t _ ⟨r₃,store w v⟩ at e₃
  have e₄ := clear_eval (port dst) (⟨r₃,store w v⟩ : State 8 (8+n))
  rw [show Function.update (store w v) (port dst) [] = store w (Function.update v dst 0) from upd_port w v dst 0] at e₄
  let r₄ := readRegs r₃ 0 1 none
  let v' := Function.update v dst 0
  have e₅ := ArithmeticCalls.copyAt_eval (low 7) (port dst) (low 1) (⟨r₄,store w v'⟩ : State 8 (8+n))
    (low_ne_port 7 dst) (fun h => (by decide : (7:Fin 8) ≠ 1) (Fin.castAdd_injective 8 n h)) (low_ne_port 1 dst)
    (by simp [v']) (by simp [w])
  change Eval _ (7*(store w v' (low 7)).length+5) _ ⟨readRegs r₄ 0 1 none,Function.update (store w v') (port dst) (store w v' (low 7))⟩ at e₅
  rw [store_low] at e₅
  change Eval _ (7*y.bits.length+5) _ ⟨_,Function.update (store w v') (port dst) y.bits⟩ at e₅
  rw [upd_port] at e₅
  have hv' : Function.update v' dst y = Function.update v dst y := Function.update_idem ..
  rw [hv'] at e₅
  let r₅ := readRegs r₄ 0 1 none
  have e₆ := clear_eval (low 7) (⟨r₅,store w (Function.update v dst y)⟩ : State 8 (8+n))
  rw [upd_low] at e₆
  have hw6 : Function.update w 7 [] = empty := by funext i; fin_cases i <;> rfl
  rw [hw6] at e₆
  refine ⟨_,_,?_,.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))⟩
  simp only [store_low,store_port,Nat.size_eq_bits_len]
  change 7*(v a).size+5+(7*(v b).size+5+(t+(2*(v dst).size+3+(7*y.size+5+(2*y.bits.length+3))))) ≤ _
  rw [Nat.size_eq_bits_len]; omega
end DetDLP.BitRegisterBank
end

section
namespace DetDLP.BitRegisterCode
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls BitArithmeticUnit
open BitRegisterBank

structure Instr (n : ℕ) where
  op : Op
  a : Fin n
  b : Fin n
  dst : Fin n

def Instr.step {n} (s : Instr n) (v : Vars n) : Vars n :=
  Function.update v s.dst (s.op.eval (v s.a) (v s.b))

def run {n} : List (Instr n) → Vars n → Vars n
  | [],v => v
  | i::is,v => run is (i.step v)
def Valid {n} : List (Instr n) → Vars n → Prop
  | [],_ => True
  | i::is,v => i.op.Valid (v i.a) ∧ Valid is (i.step v)
def compile {n} : List (Instr n) → BitRegisterBank.Code n
  | [] => .base .skip
  | s::ss => .seq (assign s.op s.a s.b s.dst) (compile ss)
abbrev frame {n} (v : Vars n) := store (fun _ => []) v

private theorem size_op (op : Op) (a b W : ℕ) (ha : a.size ≤ W) (hb : b.size ≤ W) :
    (op.eval a b).size ≤ 2*W+1 := by
  have h1 := Nat.size_le.mp ha
  have h2 := Nat.size_le.mp hb
  have hpow : 2^W ≤ 2^(2*W) := Nat.pow_le_pow_right (by decide) (by omega)
  cases op with
  | add =>
    apply Nat.size_le.mpr; change a+b < 2^(2*W+1); rw [pow_succ]; omega
  | mul =>
    have hh := Nat.mul_lt_mul_of_lt_of_le h1 h2.le (by positivity : 0 < 2^W)
    apply Nat.size_le.mpr
    change a*b < 2^(2*W+1)
    rw [two_mul,pow_succ,pow_add]; nlinarith only [hh,Nat.zero_le (2^W*2^W)]
  | quot => exact (Nat.size_le_size (Nat.div_le_self b a)).trans (by omega)
  | rem => exact (Nat.size_le_size (Nat.mod_le b a)).trans (by omega)

theorem run_eval {n} (c : List (Instr n)) (v : Vars n) (r : Regs) (W : ℕ) (hW : ∀ j, (v j).size ≤ W)
    (hv : Valid c v) :
    ∃ t rf, t ≤ 1000^(c.length+1)*(W+2)^2 ∧
      Eval (compile c) t ⟨r,frame v⟩ ⟨rf,frame (run c v)⟩ := by
  induction c generalizing v r W with
  | nil => exact ⟨0,r,Nat.zero_le _,.base (.skip _)⟩
  | cons s ss ih =>
    obtain ⟨t₁,r₁,ht₁,e₁⟩ := assign_eval s.op s.a s.b s.dst v r hv.1
    let y := s.op.eval (v s.a) (v s.b)
    have hy : y.size ≤ 2*W+1 := size_op s.op _ _ _ (hW s.a) (hW s.b)
    have hm (j : Fin n) : ((s.step v) j).size ≤ 2*W+1 := by
      by_cases h : j=s.dst
      · subst j; simpa [Instr.step] using hy
      · simp [Instr.step,h]; exact (hW j).trans (by omega)
    obtain ⟨t₂,rf,ht₂,e₂⟩ := ih (s.step v) r₁ (2*W+1) hm hv.2
    refine ⟨_,_,?_,.seq e₁ e₂⟩
    have hab := Nat.pow_le_pow_left (show (v s.a).size+(v s.b).size+1 ≤ 2*(W+2) by have := hW s.a; have := hW s.b; omega) 2
    have hsq := Nat.pow_le_pow_left (show 2*W+1+2 ≤ 2*(W+2) by omega) 2
    have hbr : 1 ≤ 1000^(ss.length+1) := Nat.one_le_pow _ _ (by decide)
    have hstep : t₁ ≤ 700*(W+2)^2 := by
      change t₁ ≤ _ + 10*( (v s.a).size + (v s.b).size + (v s.dst).size + y.size+4) at ht₁
      nlinarith only [ht₁,hab,hW s.a,hW s.b,hW s.dst,hy,Nat.zero_le (W^2),Nat.zero_le W]
    have hsub := Nat.mul_le_mul_left (1000^(ss.length+1)) hsq
    have hr := Nat.mul_le_mul_right ((W+2)^2) hbr
    change t₁+t₂ ≤ 1000^(ss.length+1+1)*(W+2)^2
    rw [pow_succ]
    nlinarith only [hstep,ht₂,hsub,hr,Nat.zero_le (1000^(ss.length+1)*(W+2)^2)]

def peek {n} (i : Fin n) : BitRegisterBank.Code n := .base (.atom (.peek (port i) 0 1))
theorem peek_eval {n} (i : Fin n) (v : Vars n) (r : Regs) :
    ∃ rf, Eval (peek i) 1 ⟨r,frame v⟩ ⟨rf,frame v⟩ ∧ rf 1 = decide (v i ≠ 0) := by
  refine ⟨readRegs r 0 1 (frame v (port i)).head?,.base (.atom _ _),?_⟩
  simp only [readRegs,Function.update_self,frame,store_port]
  cases hw : (v i).bits with
  | nil =>
    have h := (Nat.size_eq_zero (n:=v i)).mp (by rw [← Nat.size_eq_bits_len,hw]; rfl)
    simp [h]
  | cons b bs =>
    have h : v i ≠ 0 := fun e => by simp [e] at hw
    simp [h]
end DetDLP.BitRegisterCode
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
namespace DetDLP.ContinuationControl
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls BitRegisterBank BitRegisterCode ContinuationSchedule
def pending (q : ℕ) : List ℕ → ℕ
  | [] => 1
  | x::xs => pending q xs*q+x
theorem positive (q : ℕ) (hq : 0<q) (stack : List ℕ) : 0<pending q stack := by
  induction stack with
  | nil => exact Nat.zero_lt_one
  | cons x xs ih => exact Nat.add_pos_left (Nat.mul_pos ih hq) _
theorem bound (B : ℕ) (hB : 0<B) (stack : List ℕ) (small : ∀ t∈stack,t<B) :
    pending (B+1) stack < (B+1)^(stack.length+1) := by
  induction stack with
  | nil => simpa [pending]
  | cons a xs ih =>
    have cap := ih (fun t ht => small t (by simp [ht]))
    have ha := small a (by simp)
    have hh := Nat.mul_le_mul_right (B+1) (Nat.succ_le_of_lt cap)
    simp only [pending,List.length_cons,pow_succ (B+1) (xs.length+1)]
    nlinarith only [hh,ha]

def bank (q x y stk tag arg save : ℕ) : Vars 12 := ![q,1,0,x,y,stk,tag,arg,save,0,0,0]
def encoded (q : ℕ) : ContinuationSchedule.State → Vars 12
  | .eval x y stk => bank q x y (pending q stk) 0 0 0
  | .halt v => bank q 1 v 0 0 0 0
def signal (q x y stk : ℕ) : Answer → Vars 12
  | .call save child => bank q x y stk 1 child save
  | .value v => bank q x y stk 0 v 0
def ops : List (BitRegisterCode.Instr 12) :=
  [⟨.add,6,1,9⟩,⟨.quot,9,1,9⟩,⟨.rem,0,5,10⟩,⟨.mul,9,10,10⟩,⟨.mul,6,7,3⟩,⟨.add,3,10,3⟩,
   ⟨.mul,9,7,4⟩,⟨.mul,5,0,10⟩,⟨.add,10,8,10⟩,⟨.mul,10,6,10⟩,⟨.quot,0,5,11⟩,
   ⟨.mul,11,9,11⟩,⟨.add,10,11,5⟩,⟨.add,2,2,6⟩,⟨.add,2,2,7⟩,⟨.add,2,2,8⟩,
   ⟨.add,2,2,9⟩,⟨.add,2,2,10⟩,⟨.add,2,2,11⟩]
def command := (compile ops).seq (peek (5:Fin 12))
def program := compiled command (port (6:Fin 12)) (port (4:Fin 12))

def transition (q x y stk tag arg save : ℕ) :=
  let back := 1/(tag+1)
  bank q (tag*arg+back*(stk%q)) (back*arg) ((stk*q+save)*tag+(stk/q)*back) 0 0 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem calculation (q x y stk tag arg save : ℕ) (hq : 0<q) :
    Valid ops (bank q x y stk tag arg save) ∧ run ops (bank q x y stk tag arg save)=transition q x y stk tag arg save := by
  constructor
  · simp [Valid,ops,BitRegisterCode.Instr.step,BitArithmeticUnit.Op.Valid,BitArithmeticUnit.Op.eval,bank,hq,Function.update_apply]
  · funext j; fin_cases j <;> rfl

theorem result (B x y : ℕ) (hB : 0<B) (stk : List ℕ) (ans : Answer) (small : ∀ t∈stk,t<B) :
    let q := B+1
    let target := match ans with
      | .call save child => ContinuationSchedule.State.eval child 0 (save::stk)
      | .value v => deliver v stk
    Valid ops (signal q x y (pending q stk) ans) ∧ run ops (signal q x y (pending q stk) ans)=encoded q target := by
  intro q target
  cases ans with
  | call save child =>
    obtain ⟨val,eq⟩ := calculation q x y (pending q stk) 1 child save (by omega)
    refine ⟨val,?_⟩
    rw [signal,eq]; simp [transition,target,encoded,pending]
  | value v =>
    obtain ⟨val,eq⟩ := calculation q x y (pending q stk) 0 v 0 (by omega)
    refine ⟨val,?_⟩
    rw [signal,eq]
    cases stk with
    | nil =>
      have one : 1<q := by dsimp [q]; omega
      simp [transition,target,encoded,deliver,pending,Nat.mod_eq_of_lt one,Nat.div_eq_of_lt one]
    | cons a xs =>
      have ha : a<q := (small a (by simp)).trans_le (by omega)
      have hq : 0<q := by omega
      rw [show pending q (a::xs)=a+q*pending q xs by simp [pending,Nat.add_comm,Nat.mul_comm]]
      simp [transition,target,encoded,deliver,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,
        Nat.add_mul_div_left _ _ hq,Nat.div_eq_of_lt ha]

theorem flag (B : ℕ) (s : ContinuationSchedule.State) : decide (encoded (B+1) s 5≠0)=running s := by
  cases s with
  | halt v => rfl
  | eval x y stk =>
    have h := positive (B+1) (Nat.succ_pos _) stk
    change decide (pending (B+1) stk≠0)=true; simp [h.ne']
end DetDLP.ContinuationControl
end

section
namespace DetDLP.BoundedProgramLink
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
variable {r s l m : ℕ} (p : Program r s l) (q : Program r s m)
theorem relabel {L : ℕ} (Q : Program r s L) (labels : Fin l → Fin L) (ret : Option (Fin L))
    (code : CodeEmbedding p Q id id labels ret) {t x y W} (tr : SafeTrace (step p) (cap W) t x y) :
    SafeTrace (step Q) (cap W) t (relabelCfg labels ret x) (relabelCfg labels ret y) := by
  apply tr.map (relabelCfg labels ret) _ (fun _ h => h)
  intro a b h
  let frame := relabelCfg labels ret a
  simpa only [embedCfg_id] using relocate_step p Q id id labels ret frame Function.injective_id Function.injective_id code h

theorem join {n m' W : ℕ} {u v w : Fin r→Bool} {a b c : Fin s→List Bool}
    (left : SafeTrace (step p) (cap W) n ⟨some p.entry,u,a⟩ ⟨none,v,b⟩)
    (right : SafeTrace (step q) (cap W) m' ⟨some q.entry,v,b⟩ ⟨none,w,c⟩) :
    SafeTrace (step (link p q)) (cap W) (n+m') ⟨some (link p q).entry,u,a⟩ ⟨none,w,c⟩ := by
  have tr := relabel p (link p q) (Fin.castAdd m) (some (Fin.natAdd l q.entry)) (linkInto_leftCode p q id id id id) left
  have thenTr := relabel q (link p q) (Fin.natAdd l) none (linkInto_rightCode p q id id id id) right
  exact tr.trans thenTr

/-- Each callback may use fresh register values. Its own prefix bound is preserved through arbitrarily many full iterations. -/
theorem repeatBounded {S : Type} (flag : Fin r) (f : S→S) (ongoing : S→Bool) (V : S→Fin s→List Bool)
    (W : ℕ) (budget : S→ℕ) (n : ℕ) (z : S) (reg : Fin r→Bool)
    (flag0 : reg flag=ongoing z) (stop : ongoing (f^[n] z)=false)
    (mem : ∀ j,j≤n → ∀ i,(V (f^[j] z) i).length≤W)
    (blocks : ∀ j,j<n → let s := f^[j] z
      ongoing s=true ∧ ∀ r0 : Fin r→Bool,r0 flag=true →
        ∃ t r1,t ≤ budget s ∧ r1 flag=ongoing (f s) ∧
          SafeTrace (step p) (cap W) t ⟨some p.entry,r0,V s⟩ ⟨none,r1,V (f s)⟩) :
    ∃ t rf,t ≤ 2+n+∑ j∈Finset.range n,budget (f^[j] z) ∧
      SafeTrace (step (loop p flag)) (cap W) t
        ⟨some (loop p flag).entry,reg,V z⟩ ⟨none,rf,V (f^[n] z)⟩ := by
  induction n generalizing z reg with
  | zero =>
    have space := mem 0 (by omega)
    let c : Cfg r s (2+l) := ⟨some head,reg,V z⟩
    have h := test p flag c rfl
    change ongoing z=false at stop
    simp only [c,flag0,stop,Bool.false_eq_true,if_false] at h
    exact ⟨2,reg,by simp,.cons space h (.cons space (halt p flag _ rfl) (.refl _ space))⟩
  | succ n ih =>
    obtain ⟨yes,call⟩ := blocks 0 (by omega)
    obtain ⟨t,reg',cost,hreg,tr⟩ := call reg (flag0.trans yes)
    let c : Cfg r s (2+l) := ⟨some head,reg,V z⟩
    have h := test p flag c rfl
    have yes' : ongoing z=true := yes
    simp only [c,flag0,yes',if_true] at h
    have before := SafeTrace.cons (show cap W c from mem 0 (by omega)) h (block p flag tr)
    obtain ⟨k,rf,time,rest⟩ := ih (f z) reg' hreg (by simpa only [Function.iterate_succ_apply] using stop)
      (fun j hj => by simpa only [Function.iterate_succ_apply] using mem (j+1) (by omega))
      (fun j hj => by simpa only [Function.iterate_succ_apply] using blocks (j+1) (by omega))
    refine ⟨(t+1)+k,rf,?_,before.trans rest⟩
    rw [Finset.sum_range_succ']; simp only [Function.iterate_succ_apply,Function.iterate_zero_apply] at *
    omega
end DetDLP.BoundedProgramLink
end

section
namespace DetDLP.ContinuationControlTrace
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls BitRegisterBank BitRegisterCode
open BoundedProgramLoop ContinuationSchedule ContinuationControl
def allowed (B : ℕ) : Answer → Prop
  | .call save child => save<B ∧ child<B
  | .value v => v<B
def action (stack : List ℕ) : Answer → ContinuationSchedule.State
  | .call save child => .eval child 0 (save::stack)
  | .value v => deliver v stack
theorem bounded_action {B D : ℕ} (stack : List ℕ) (a : Answer) (h : bounded B D (action stack a)) : allowed B a := by
  cases a with
  | call save child => exact ⟨h.2.2.2 save (by simp),h.1⟩
  | value v => cases stack with
    | nil => exact h
    | cons t ts => exact h.2.1

def W (B D : ℕ) := (B+1).size*(D+1)+1
def ctrl (B D : ℕ) := (1000^(ops.length+1)+5)*(W B D+2)^2
theorem bank_size (q x y stk tag arg save N W : ℕ) (pos : 1≤N)
    (h : q≤N ∧ x≤N ∧ y≤N ∧ stk≤N ∧ tag≤N ∧ arg≤N ∧ save≤N)
    (size : N.size≤W) : ∀ i,(bank q x y stk tag arg save i).size≤W := by
  intro i; apply le_trans _ size
  apply Nat.size_le_size; fin_cases i <;> dsimp [bank] <;> omega

theorem stk_size {B D : ℕ} (hB : 0<B) (stack : List ℕ) (small : validStack B D stack) :
    let N := (B+1)^(D+1)
    B+1≤N ∧ N.size≤W B D ∧ pending (B+1) stack≤N := by
  intro N
  have hq : 0<B+1 := Nat.succ_pos _
  refine ⟨Nat.le_self_pow (by omega) _,?_,?_⟩
  · apply Nat.size_le.mpr
    have a := Nat.pow_lt_pow_left (Nat.lt_size_self (B+1)) (by omega : D+1 ≠ 0)
    rw [←pow_mul] at a
    exact a.trans_le (Nat.pow_le_pow_right (by decide) (by unfold W; omega))
  · exact (bound B hB stack small.2).le.trans (Nat.pow_le_pow_right hq (Nat.add_le_add_right small.1 1))

theorem words (B D : ℕ) (hB : 0<B) (x y : ℕ) (stk : List ℕ) (a : Answer)
    (old : bounded B D (.eval x y stk)) (ha : allowed B a) :
    let z := signal (B+1) x y (pending (B+1) stk) a
    ∀ i,(z i).size≤W B D := by
  intro z
  obtain ⟨b,sz,s⟩ := stk_size hB stk old.2.2
  have xlt := old.1
  have ylt := old.2.1
  cases a with
  | value v =>
    change v<B at ha
    exact bank_size _ _ _ _ _ _ _ _ _ (by omega) (by omega) sz
  | call save child =>
    change save<B ∧ child<B at ha
    exact bank_size _ _ _ _ _ _ _ _ _ (by omega) (by omega) sz

theorem frame_size (v : Vars 12) (w : ℕ) (hv : ∀ i,(v i).size≤w) :
    ∀ l,(frame v l).length≤w := by
  intro l; refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [show frame v (Fin.castAdd 12 i)=[] from store_low ..]; simp
  · rw [show frame v (Fin.natAdd 8 i)=(v i).bits from store_port ..,Nat.size_eq_bits_len]; exact hv i

theorem run (B D : ℕ) (hB : 0<B) (x y : ℕ) (stk : List ℕ) (a : Answer)
    (old : bounded B D (.eval x y stk)) (ha : allowed B a) (regs : Fin 8→Bool) :
    let z := signal (B+1) x y (pending (B+1) stk) a
    let next := action stk a
    ∃ t rf,t≤ctrl B D ∧ rf 1=running next ∧
      SafeTrace (step program) (cap (ctrl B D)) t ⟨some program.entry,regs,frame z⟩
        ⟨none,rf,frame (encoded (B+1) next)⟩ := by
  intro z next
  obtain ⟨valid,effect⟩ := result B x y hB stk a old.2.2.2
  have all := words B D hB x y stk a old ha
  obtain ⟨t,rf,ht,ev⟩ := run_eval ops z regs (W B D) all valid
  change BitRegisterCode.run ops z=encoded (B+1) next at effect
  rw [effect] at ev
  obtain ⟨rf',after,hflag⟩ := peek_eval (5:Fin 12) (encoded (B+1) next) rf
  have tr := compiled_halt_trace (Eval.seq ev after) (port (6:Fin 12)) (port (4:Fin 12))
  have cap : W B D+(t+1+1)≤ctrl B D := by
    unfold ctrl
    nlinarith only [ht,Nat.zero_le (W B D),Nat.zero_le ((W B D)^2)]
  refine ⟨_,rf',by omega,hflag.trans (flag B next),SafeTrace.of_trace tr ?_⟩
  intro j c hj prefixTrace i
  have h := BitTracePolynomial.trace_grows prefixTrace i
  exact h.trans ((Nat.add_le_add (frame_size z _ all i) hj).trans cap)
end DetDLP.ContinuationControlTrace
end

section
namespace DetDLP.ContinuationDriver
open Finset OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BitRegisterCode
open BoundedProgramLoop BoundedProgramLink ContinuationSchedule ContinuationControl ContinuationControlTrace
variable {l : ℕ} (callback : Program 8 20 l)
def combined := link callback ContinuationControl.program
def machine := loop (combined callback) (1:Fin 8)

theorem mono {r s l W W' : ℕ} {p : Program r s l} {n : ℕ} {x y : Cfg r s l}
    (h : SafeTrace (step p) (cap W) n x y) (le : W≤W') : SafeTrace (step p) (cap W') n x y :=
  h.map id (fun _ _ h => h) (fun _ h i => (h i).trans le)

theorem state_mem (B D : ℕ) (hB : 0<B) (s : ContinuationSchedule.State) (v : bounded B D s) :
    ∀ i,(frame (encoded (B+1) s) i).length ≤ W B D := by
  apply frame_size
  cases s with
  | eval x y stk => exact words B D hB x y stk (.value 0) v hB
  | halt z =>
    obtain ⟨q,size,_⟩ := stk_size hB ([]:List ℕ) (show validStack B D [] by simp [validStack])
    change z<B at v
    exact bank_size _ _ _ _ _ _ _ _ _ (by omega) (by omega) size

theorem run (F : ℕ → ℕ → Answer) (B T U : ℕ) (hB : 0<B)
    (x y value n D : ℕ) (correct : Computes F B x y value n D)
    (service : ∀ (x y st : ℕ) (regs : Fin 8→Bool),x<B → y<B → st < (B+1)^(D+1) →
      allowed B (F x y) → ∃ t rf,t≤T ∧
      SafeTrace (step callback) (cap U) t
        ⟨some callback.entry,regs,frame (bank (B+1) x y st 0 0 0)⟩
        ⟨none,rf,frame (signal (B+1) x y st (F x y))⟩)
    (regs : Fin 8→Bool) (flag0 : regs 1=true) :
    let M := machine callback
    let peak := max U (max (W B D) (ctrl B D))
    ∃ t rf,t≤2+n*(1+T+ctrl B D) ∧
      SafeTrace (step M) (cap peak) t ⟨some M.entry,regs,frame (bank (B+1) x y 1 0 0 0)⟩
        ⟨none,rf,frame (bank (B+1) 1 value 0 0 0 0)⟩ := by
  intro M peak
  let start := ContinuationSchedule.State.eval x y []
  obtain ⟨finish,valid,early⟩ := outcome correct
  let repr (s : ContinuationSchedule.State) := frame (encoded (B+1) s)
  obtain ⟨t,rf,time,trace⟩ := repeatBounded (combined callback) (1:Fin 8) (advance F) running repr
    peak (fun _ => T+ctrl B D) n start regs flag0 (by rw [finish]; rfl)
    (fun j hj i => (state_mem B D hB _ (valid j hj) i).trans ((le_max_left ..).trans (le_max_right ..)))
    (by
      intro j hj z
      refine ⟨early j hj,?_⟩; intro reg flag
      have vz : bounded B D z := valid j hj.le
      have ongoing : running z=true := early j hj
      have vy : bounded B D (advance F z) := by
        have H := valid (j+1) (by omega)
        simpa only [Function.iterate_succ_apply'] using H
      cases eq : z with
      | halt v => rw [eq] at ongoing; contradiction
      | eval a b stk =>
        rw [eq] at vz vy
        let act := F a b
        have actual : advance F (.eval a b stk)=action stk act := by
          dsimp [act,advance]; cases F a b <;> rfl
        rw [actual] at vy ⊢
        have ha := bounded_action stk act vy
        have ss := (ContinuationControl.bound B hB stk vz.2.2.2).trans_le
          (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.add_le_add_right vz.2.2.1 1))
        obtain ⟨k,reg',time,tr⟩ := service a b (pending (B+1) stk) reg vz.1 vz.2.1 ss ha
        obtain ⟨m,r',mt,flag',ct⟩ := ContinuationControlTrace.run B D hB a b stk act vz ha reg'
        refine ⟨k+m,r',Nat.add_le_add time mt,flag',?_⟩
        apply BoundedProgramLink.join callback ContinuationControl.program
          (mono tr (le_max_left ..)) (mono ct ((le_max_right ..).trans (le_max_right ..))))
  rw [finish] at trace
  refine ⟨t,rf,time.trans ?_,trace⟩
  apply le_of_eq
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id]; ring
end DetDLP.ContinuationDriver
end

section
namespace DetDLP.StackSpaceLift
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
variable {r s l u : ℕ} (p : Program r s l)
def append (ctx : Fin u→List Bool) (c : Cfg r s l) : Cfg r (s+u) l :=
  ⟨c.pc,c.regs,Fin.addCases c.stacks ctx⟩
private theorem extCfg {r s l : ℕ} {a b : Cfg r s l} (pc : a.pc=b.pc) (rg : a.regs=b.regs) (st : a.stacks=b.stacks) : a=b := by
  cases a; cases b; congr
theorem safe (ctx : Fin u→List Bool) (W : ℕ) (hc : ∀ i,(ctx i).length ≤ W)
    {n a b} (tr : SafeTrace (step p) (cap W) n a b) :
    SafeTrace (step (liftProgram p id (Fin.castAdd u))) (cap W) n (append ctx a) (append ctx b) := by
  let ext := Fin.castAdd (n:=s) u
  let base : Cfg r (s+u) l := append ctx a
  have eq (z : Cfg r s l) : embedCfg id ext id none base z=append ctx z := by
    apply extCfg
    · cases hp : z.pc <;> simp [embedCfg,append,relocatePc,hp]
    · simp [embedCfg,append]
    · funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [append,Fin.addCases_left] using embedCfg_stack id ext id none base z (Fin.castAdd_injective ..) j
      · have out : ¬ ∃ x,ext x=Fin.natAdd s j := by
          rintro ⟨x,h⟩; have h' := congrArg Fin.val h
          change x.val=s+j.val at h'; have := x.isLt; omega
        rw [embedCfg_stack_frame id ext id none base _ _ out]
        simp [base,append]
  refine tr.map (append ctx) ?_ ?_
  · intro x y h; rw [←eq,←eq]
    exact relocate_step p _ id ext id none base Function.injective_id (Fin.castAdd_injective ..) (fun _ => rfl) h
  · intro z ok i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [append] using ok j
    · simpa [append] using hc j
end DetDLP.StackSpaceLift
end

section
namespace DetDLP.ContinuationContextDriver
open Finset OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BitRegisterCode
open BoundedProgramLoop BoundedProgramLink ContinuationSchedule ContinuationControl ContinuationControlTrace
variable {l u : ℕ} (callback : Program 8 (20+u) l)
def data (ctx : Fin u→List Bool) (v : BitRegisterBank.Vars 12) : Fin (20+u)→List Bool := Fin.addCases (frame v) ctx
def combined := link callback (liftProgram ContinuationControl.program id (Fin.castAdd u))
def machine := loop (combined callback) (1:Fin 8)
theorem run (ctx : Fin u→List Bool) (F : ℕ → ℕ → Answer) (B T U : ℕ) (hB : 0<B) (hctx : ∀ i,(ctx i).length≤U)
    (x y value n D : ℕ) (correct : Computes F B x y value n D)
    (service : ∀ (x y st : ℕ) (regs : Fin 8→Bool),x<B → y<B → st < (B+1)^(D+1) →
      allowed B (F x y) → ∃ t rf,t≤T ∧
      SafeTrace (step callback) (cap U) t
        ⟨some callback.entry,regs,data ctx (bank (B+1) x y st 0 0 0)⟩
        ⟨none,rf,data ctx (signal (B+1) x y st (F x y))⟩)
    (regs : Fin 8→Bool) (flag0 : regs 1=true) :
    let M := machine callback
    let peak := max U (max (W B D) (ctrl B D))
    ∃ t rf,t≤2+n*(1+T+ctrl B D) ∧
      SafeTrace (step M) (cap peak) t ⟨some M.entry,regs,data ctx (bank (B+1) x y 1 0 0 0)⟩
        ⟨none,rf,data ctx (bank (B+1) 1 value 0 0 0 0)⟩ := by
  intro M peak
  let start := ContinuationSchedule.State.eval x y []
  obtain ⟨finish,valid,early⟩ := outcome correct
  let repr (s : ContinuationSchedule.State) := data ctx (encoded (B+1) s)
  obtain ⟨t,rf,time,trace⟩ := repeatBounded (combined callback) (1:Fin 8) (advance F) running repr
    peak (fun _ => T+ctrl B D) n start regs flag0 (by rw [finish]; rfl)
    (by
      intro j hj i
      refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [repr,data,Fin.addCases_left] using
          (ContinuationDriver.state_mem B D hB _ (valid j hj) l).trans ((le_max_left ..).trans (le_max_right ..))
      · simpa only [repr,data,Fin.addCases_right] using (hctx l).trans (le_max_left ..))
    (by
      intro j hj z
      refine ⟨early j hj,?_⟩; intro reg flag
      have vz : bounded B D z := valid j hj.le
      have ongoing : running z=true := early j hj
      have vy : bounded B D (advance F z) := by
        have H := valid (j+1) (by omega)
        simpa only [Function.iterate_succ_apply'] using H
      cases eq : z with
      | halt v => rw [eq] at ongoing; contradiction
      | eval a b stk =>
        rw [eq] at vz vy
        let act := F a b
        have actual : advance F (.eval a b stk)=action stk act := by
          dsimp [act,advance]; cases F a b <;> rfl
        rw [actual] at vy ⊢
        have ha := bounded_action stk act vy
        have ss := (ContinuationControl.bound B hB stk vz.2.2.2).trans_le
          (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.add_le_add_right vz.2.2.1 1))
        obtain ⟨k,reg',time,tr⟩ := service a b (pending (B+1) stk) reg vz.1 vz.2.1 ss ha
        obtain ⟨m,r',mt,flag',ct⟩ := ContinuationControlTrace.run B D hB a b stk act vz ha reg'
        refine ⟨k+m,r',Nat.add_le_add time mt,flag',?_⟩
        let wide := StackSpaceLift.safe ContinuationControl.program ctx peak (fun i => (hctx i).trans (le_max_left ..))
          (ContinuationDriver.mono ct ((le_max_right ..).trans (le_max_right ..)))
        exact BoundedProgramLink.join callback (liftProgram ContinuationControl.program id (Fin.castAdd u))
          (ContinuationDriver.mono tr (le_max_left ..)) wide)
  rw [finish] at trace
  refine ⟨t,rf,time.trans ?_,trace⟩
  apply le_of_eq
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id]; ring
end DetDLP.ContinuationContextDriver
end

section
namespace DetDLP.ContinuationMachineExport
open OAI.Algorithms.SubexponentialSAT DetDLP.ContinuationSchedule
set_option maxRecDepth 6000 in
theorem full {s l : ℕ} (Q : BitProgram.Program 8 (20+s) l) :
    ∃ (labels L : ℕ) (M : BitProgram.Program 8 (20+s) labels),∀ (context : Fin s→List Bool)
      (F : ℕ→ℕ→Answer) (B T U : ℕ) (x y value calls depth : ℕ),
      0<B → (∀ i,(context i).length≤U) → Computes F B x y value calls depth →
      let q := B+1
      let pack (a b stack tag arg save : ℕ) : Fin (20+s)→List Bool :=
        let v : Fin 12→ℕ := ![q,1,0,a,b,stack,tag,arg,save,0,0,0]
        Fin.addCases (m:=20) (n:=s) (Fin.addCases (m:=8) (n:=12) (fun _ => []) (fun j => (v j).bits)) context
      let small (z : Answer) := match z with
        | .value v => v<B
        | .call a b => a<B ∧ b<B
      let returned (a b stack : ℕ) (z : Answer) := match z with
        | .value v => pack a b stack 0 v 0
        | .call save child => pack a b stack 1 child save
      (∀ (a b stack : ℕ) (r : Fin 8→Bool),a<B → b<B → stack < q^(depth+1) → small (F a b) →
        let start : BitProgram.Cfg 8 (20+s) l := ⟨some Q.entry,r,pack a b stack 0 0 0⟩
        ∃ (steps : ℕ) (r' : Fin 8→Bool),steps≤T ∧
          BitProgram.Trace Q steps start ⟨none,r',returned a b stack (F a b)⟩ ∧
          ∀ j c,j≤ steps → BitProgram.Trace Q j start c → ∀ i,(c.stacks i).length≤U) →
      ∀ (r : Fin 8→Bool),r 1=true →
      let start : BitProgram.Cfg 8 (20+s) labels := ⟨some M.entry,r,pack x y 1 0 0 0⟩
      let overhead := L*(q.size*(depth+1)+3)^2
      ∃ (steps : ℕ) (rf : Fin 8→Bool),steps≤2+calls*(1+T+overhead) ∧
        BitProgram.Trace M steps start ⟨none,rf,pack 1 value 0 0 0 0⟩ ∧
        ∀ j c,j≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ max U overhead := by
  let K := 1000^(ContinuationControl.ops.length+1)+5
  refine ⟨_,K,ContinuationContextDriver.machine Q,?_⟩
  intro ctx F B T U x y value calls depth hB hctx proof q pack small returned service reg flag start overhead
  have eq (a b st : ℕ) (ans : Answer) : returned a b st ans =
      ContinuationContextDriver.data ctx (ContinuationControl.signal q a b st ans) := by cases ans <;> rfl
  have allow (ans : Answer) : ContinuationControlTrace.allowed B ans → small ans := by cases ans <;> exact id
  obtain ⟨t,rf,ht,tr⟩ := ContinuationContextDriver.run Q ctx F B T U hB hctx x y value calls depth proof
    (by intro a b st r ha hb hs spec
        obtain ⟨k,rr,time,tk,cap⟩ := service a b st r ha hb hs (allow _ spec)
        refine ⟨k,rr,time,?_⟩
        rw [eq] at tk
        exact BoundedProgramLoop.SafeTrace.of_trace tk cap) reg flag
  have ctl : ContinuationControlTrace.ctrl B depth=overhead := by rfl
  have wle : ContinuationControlTrace.W B depth≤overhead := by
    rw [←ctl]; unfold ContinuationControlTrace.ctrl
    nlinarith only [Nat.zero_le (ContinuationControlTrace.W B depth),Nat.zero_le ((ContinuationControlTrace.W B depth)^2),
      Nat.zero_le (1000^(ContinuationControl.ops.length+1)*(ContinuationControlTrace.W B depth+2)^2)]
  rw [ctl] at ht tr
  rw [max_eq_right wle] at tr
  exact ⟨t,rf,ht,tr.forget,tr.within⟩
end DetDLP.ContinuationMachineExport
end

open DetDLP
open OAI.Algorithms.SubexponentialSAT DetDLP.ContinuationSchedule

set_option maxRecDepth 6000 in
theorem solution {s l : ℕ} (Q : BitProgram.Program 8 (20+s) l) :
    ∃ (labels L : ℕ) (M : BitProgram.Program 8 (20+s) labels),∀ (context : Fin s→List Bool)
      (F : ℕ→ℕ→Answer) (B T U : ℕ) (x y value calls depth : ℕ),
      0<B → (∀ i,(context i).length≤U) → Computes F B x y value calls depth →
      let q := B+1
      let pack (a b stack tag arg save : ℕ) : Fin (20+s)→List Bool :=
        let v : Fin 12→ℕ := ![q,1,0,a,b,stack,tag,arg,save,0,0,0]
        Fin.addCases (m:=20) (n:=s) (Fin.addCases (m:=8) (n:=12) (fun _ => []) (fun j => (v j).bits)) context
      let small (z : Answer) := match z with
        | .value v => v<B
        | .call a b => a<B ∧ b<B
      let returned (a b stack : ℕ) (z : Answer) := match z with
        | .value v => pack a b stack 0 v 0
        | .call save child => pack a b stack 1 child save
      (∀ (a b stack : ℕ) (r : Fin 8→Bool),a<B → b<B → stack < q^(depth+1) → small (F a b) →
        let start : BitProgram.Cfg 8 (20+s) l := ⟨some Q.entry,r,pack a b stack 0 0 0⟩
        ∃ (steps : ℕ) (r' : Fin 8→Bool),steps≤T ∧
          BitProgram.Trace Q steps start ⟨none,r',returned a b stack (F a b)⟩ ∧
          ∀ j c,j≤ steps → BitProgram.Trace Q j start c → ∀ i,(c.stacks i).length≤U) →
      ∀ (r : Fin 8→Bool),r 1=true →
      let start : BitProgram.Cfg 8 (20+s) labels := ⟨some M.entry,r,pack x y 1 0 0 0⟩
      let overhead := L*(q.size*(depth+1)+3)^2
      ∃ (steps : ℕ) (rf : Fin 8→Bool),steps≤2+calls*(1+T+overhead) ∧
        BitProgram.Trace M steps start ⟨none,rf,pack 1 value 0 0 0 0⟩ ∧
        ∀ j c,j≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ max U overhead := by
  exact ContinuationMachineExport.full Q
