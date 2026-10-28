-- Prove2me | solution 1 for BitDFT.binary_counter_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:50:58.631957+00:00
-- url     : https://prove2.me/submissions/c22eb590-d8e2-4375-92e3-7e9583d2a717

import Definitions.Def_BitDFT_BinaryCounter
namespace BitDFT.BinaryCounter
open IntMul

private theorem protect_self (a : Sym) : HeaderReader.protect a (a,.stay) = (a,.stay) := by
  cases a <;> rfl
theorem increment_value (w : List Bool) : value (increment w) = value w + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [increment,value,ih] <;> omega

theorem increment_potential (w : List Bool) : ones (increment w) + lowOnes w = ones w + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [increment,lowOnes,ones] at * <;> omega

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem erase_last (k : ℕ) :
    Function.update (machine.tapeOf (List.replicate (k+1) TapeCopy.Sym.one)) (k+1) TapeCopy.Sym.blank =
    machine.tapeOf (List.replicate k TapeCopy.Sym.one) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = k
    · subst p; simp [MultitapeTM.tapeOf]
    · rw [Function.update_of_ne (by omega : p+1 ≠ k+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hl : p < k
      · simp [List.getD_replicate, hl, show p < k+1 by omega]
      · simp [List.getD_replicate, hl, show ¬p < k+1 by omega]

private theorem tick_step (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    machine.step (frame base .tick w (k+1) 1) = frame base .carry w k 1 := by
  let c := frame base .tick w (k+1) 1
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.one := by
    simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.carry, fun i => if i = 3 then (TapeCopy.Sym.blank,Move.left) else (c.cells i (c.head i),Move.stay)) := by
    apply Prod.ext
    · simp [transition,raw,show c.state = State.tick from rfl,h3]
    · funext i
      by_cases hi : i = 3
      · subst i; simp [transition,raw,c,frame,h3,HeaderReader.protect,MultitapeTM.tapeOf]
      · simp [transition,raw,show c.state = State.tick from rfl,h3,hi,protect_self]
  change machine.step c = _
  apply cfg_ext
  · simp [MultitapeTM.step,ht,frame]
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact erase_last k
  · simp only [MultitapeTM.step,ht]
    funext i; fin_cases i <;> simp [c,frame]


private def movePos (d : Move) (hp : ℕ) : ℕ :=
  match d with | .left => hp-1 | .stay => hp | .right => hp+1

private theorem work_step (base : machine.Cfg) (q q' : State) (w w' : List Bool)
    (k hp hp' : ℕ) (a : Sym) (d : Move)
    (ht : transition q (fun i => (frame base q w k hp).cells i ((frame base q w k hp).head i)) =
      (q',fun i => if i = 2 then (a,d) else
        ((frame base q w k hp).cells i ((frame base q w k hp).head i),Move.stay)))
    (hw : Function.update (machine.tapeOf (w.map machine.bitSym)) hp a =
      machine.tapeOf (w'.map machine.bitSym))
    (hm : movePos d hp = hp') :
    machine.step (frame base q w k hp) = frame base q' w' k hp' := by
  let c := frame base q w k hp
  change transition c.state (fun i => c.cells i (c.head i)) = _ at ht
  change machine.step c = _
  apply cfg_ext
  · simp [MultitapeTM.step,ht,frame]
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact hw
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · rfl
    · rfl
    · cases d <;> simpa [c,frame,movePos] using hm
    · rfl

private theorem tape_replace (pre rest : List Sym) (a b : Sym) :
    Function.update (machine.tapeOf (pre ++ a::rest)) (pre.length+1) b =
      machine.tapeOf (pre ++ b::rest) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = pre.length
    · subst p; simp [MultitapeTM.tapeOf,List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ pre.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hl : p < pre.length
      · rw [List.getD_append _ _ _ _ hl,List.getD_append _ _ _ _ hl]
      · have hg : pre.length ≤ p := by omega
        rw [List.getD_append_right _ _ _ _ hg,List.getD_append_right _ _ _ _ hg]
        have hn : p-pre.length = (p-pre.length-1)+1 := by omega
        rw [hn]
        rfl

private theorem tape_append (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length+1) a = machine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = w.length
    · subst p; simp [MultitapeTM.tapeOf,List.getD_append_right]
    · rw [Function.update_of_ne (by omega : p+1 ≠ w.length+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hl : p < w.length
      · rw [List.getD_append _ _ _ _ hl]
      · have hg : w.length ≤ p := by omega
        rw [List.getD_eq_default _ _ hg,List.getD_append_right _ _ _ _ hg]
        exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem carry_one (base : machine.Cfg) (pre rest : List Bool) (k : ℕ) :
    machine.step (frame base .carry (pre++true::rest) k (pre.length+1)) =
      frame base .carry (pre++false::rest) k (pre.length+2) := by
  let c := frame base .carry (pre++true::rest) k (pre.length+1)
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.one := by
    simp [c,frame,MultitapeTM.tapeOf,MultitapeTM.bitSym]
  refine work_step base .carry .carry _ _ k (pre.length+1) (pre.length+2) .zero .right ?_ ?_ ?_
  · change transition c.state (fun i => c.cells i (c.head i)) = _
    apply Prod.ext
    · simp [transition,raw,show c.state = State.carry from rfl,h2]
    · funext i
      by_cases hi : i = 2
      · subst i; simp [transition,raw,show c.state = State.carry from rfl,h2,HeaderReader.protect]
      · simp [transition,raw,show c.state = State.carry from rfl,h2,hi,protect_self] <;> rfl
  · simpa [List.map_append,MultitapeTM.bitSym] using
      tape_replace (pre.map machine.bitSym) (rest.map machine.bitSym) .one .zero
  · simp [movePos]


private theorem carry_finish (base : machine.Cfg) (w w' : List Bool) (k hp : ℕ)
    (hr : machine.tapeOf (w.map machine.bitSym) hp = TapeCopy.Sym.zero ∨
      machine.tapeOf (w.map machine.bitSym) hp = TapeCopy.Sym.blank)
    (hw : Function.update (machine.tapeOf (w.map machine.bitSym)) hp TapeCopy.Sym.one =
      machine.tapeOf (w'.map machine.bitSym)) :
    machine.step (frame base .carry w k hp) = frame base .rewind w' k (hp-1) := by
  let c := frame base .carry w k hp
  refine work_step base .carry .rewind w w' k hp (hp-1) .one .left ?_ hw rfl
  change transition c.state (fun i => c.cells i (c.head i)) = _
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.zero ∨
      c.cells 2 (c.head 2) = TapeCopy.Sym.blank := hr
  apply Prod.ext
  · rcases h2 with h2 | h2 <;> simp [transition,raw,show c.state = State.carry from rfl,h2]
  · funext i
    by_cases hi : i = 2
    · subst i
      rcases h2 with h2 | h2 <;>
        simp [transition,raw,show c.state = State.carry from rfl,h2,HeaderReader.protect]
    · rcases h2 with h2 | h2 <;>
        simp [transition,raw,show c.state = State.carry from rfl,h2,hi,protect_self] <;> rfl

private theorem tape_nonstart (w : List Bool) (p : ℕ) :
    machine.tapeOf (w.map machine.bitSym) (p+1) ≠ TapeCopy.Sym.start := by
  simp only [MultitapeTM.tapeOf]
  by_cases h : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
    cases w[p] <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    decide

private theorem rewind_step (base : machine.Cfg) (w : List Bool) (k p : ℕ) :
    machine.step (frame base .rewind w k (p+1)) = frame base .rewind w k p := by
  let c := frame base .rewind w k (p+1)
  have h2 : c.cells 2 (c.head 2) ≠ TapeCopy.Sym.start := tape_nonstart w p
  refine work_step base .rewind .rewind w w k (p+1) p
    (machine.tapeOf (w.map machine.bitSym) (p+1)) .left ?_ (Function.update_eq_self _ _) (by simp [movePos])
  change transition c.state (fun i => c.cells i (c.head i)) = _
  apply Prod.ext
  · simp [transition,raw,show c.state = State.rewind from rfl,h2]
  · funext i
    by_cases hi : i = 2
    · subst i
      change HeaderReader.protect (c.cells 2 (c.head 2))
        ((raw c.state _).2 2) = _
      simp [raw,show c.state = State.rewind from rfl,h2,HeaderReader.protect]
      rfl
    · simp [transition,raw,show c.state = State.rewind from rfl,h2,hi,protect_self] <;> rfl

private theorem rewind_zero (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    machine.step (frame base .rewind w k 0) = frame base .tick w k 1 := by
  let c := frame base .rewind w k 0
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.start := rfl
  refine work_step base .rewind .tick w w k 0 1 .start .right ?_ (Function.update_eq_self _ _) rfl
  change transition c.state (fun i => c.cells i (c.head i)) = _
  apply Prod.ext
  · simp [transition,raw,show c.state = State.rewind from rfl,h2]
  · funext i
    by_cases hi : i = 2
    · subst i; simp [transition,raw,show c.state = State.rewind from rfl,h2,HeaderReader.protect]
    · simp [transition,raw,show c.state = State.rewind from rfl,h2,hi,protect_self] <;> rfl

private theorem rewind_run (base : machine.Cfg) (w : List Bool) (k p : ℕ) :
    machine.step^[p+1] (frame base .rewind w k p) = frame base .tick w k 1 := by
  induction p with
  | zero => simpa using rewind_zero base w k
  | succ p ih => rw [Function.iterate_succ_apply,rewind_step,ih]


private theorem carry_nil (base : machine.Cfg) (pre : List Bool) (k : ℕ) :
    machine.step (frame base .carry pre k (pre.length+1)) =
      frame base .rewind (pre++[true]) k pre.length := by
  apply carry_finish
  · right; simp [MultitapeTM.tapeOf]
  · simpa [List.map_append,MultitapeTM.bitSym] using tape_append (pre.map machine.bitSym) .one

private theorem carry_zero (base : machine.Cfg) (pre rest : List Bool) (k : ℕ) :
    machine.step (frame base .carry (pre++false::rest) k (pre.length+1)) =
      frame base .rewind (pre++true::rest) k pre.length := by
  apply carry_finish
  · left; simp [MultitapeTM.tapeOf,MultitapeTM.bitSym]
  · simpa [List.map_append,MultitapeTM.bitSym] using
      tape_replace (pre.map machine.bitSym) (rest.map machine.bitSym) .zero .one

private theorem carry_run (base : machine.Cfg) (pre w : List Bool) (k : ℕ) :
    machine.step^[2*lowOnes w+pre.length+2]
      (frame base .carry (pre++w) k (pre.length+1)) =
      frame base .tick (pre++increment w) k 1 := by
  induction w generalizing pre with
  | nil =>
    simp only [lowOnes,increment,Nat.mul_zero,Nat.zero_add,List.append_nil]
    rw [show pre.length+2=(pre.length+1)+1 by omega,Function.iterate_succ_apply,carry_nil]
    exact rewind_run base _ k pre.length
  | cons b w ih =>
    cases b with
    | false =>
      simp only [lowOnes,increment,Nat.mul_zero,Nat.zero_add]
      rw [show pre.length+2=(pre.length+1)+1 by omega,Function.iterate_succ_apply,carry_zero]
      exact rewind_run base _ k pre.length
    | true =>
      simp only [lowOnes,increment]
      rw [show 2*(lowOnes w+1)+pre.length+2 = (2*lowOnes w+(pre++[false]).length+2)+1
        by simp; omega, Function.iterate_succ_apply,carry_one]
      simpa [List.append_assoc] using ih (pre++[false])

private theorem cycle_run (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    machine.step^[2*lowOnes w+3] (frame base .tick w (k+1) 1) =
      frame base .tick (increment w) k 1 := by
  rw [show 2*lowOnes w+3=(2*lowOnes w+2)+1 by omega,Function.iterate_succ_apply,tick_step]
  simpa using carry_run base [] w k

def clock : List Bool → ℕ → ℕ
  | _, 0 => 0
  | w, k+1 => 2*lowOnes w+3+clock (increment w) k

theorem count_run (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    machine.step^[clock w k] (frame base .tick w k 1) =
      frame base .tick (increment^[k] w) 0 1 := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [clock, Nat.add_comm, Function.iterate_add_apply,cycle_run,ih,
      Function.iterate_succ_apply]

theorem clock_potential (w : List Bool) (k : ℕ) :
    clock w k + 2*ones (increment^[k] w) = 5*k + 2*ones w := by
  induction k generalizing w with
  | zero => simp [clock]
  | succ k ih =>
    rw [clock,Function.iterate_succ_apply]
    have h := ih (increment w)
    have hp := increment_potential w
    omega

theorem count_value (w : List Bool) (k : ℕ) : value (increment^[k] w) = value w+k := by
  induction k generalizing w with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply,ih,increment_value]; omega

private theorem tick_zero (base : machine.Cfg) (w : List Bool) :
    machine.step (frame base .tick w 0 1) = frame base .halt w 0 1 := by
  let c := frame base .tick w 0 1
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.start := rfl
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt,fun i => (c.cells i (c.head i),Move.stay)) := by
    apply Prod.ext
    · simp [transition,raw,show c.state = State.tick from rfl,h3]
    · funext i; simp [transition,raw,show c.state = State.tick from rfl,h3,protect_self]
  change machine.step c = _
  apply cfg_ext
  · simp [MultitapeTM.step,ht,frame]
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i; exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]; rfl

end BitDFT.BinaryCounter

open BitDFT.BinaryCounter IntMul

/-- Exact addition by a unary count, with amortized linear actual-machine time. -/
theorem solution (base : machine.Cfg) (w : List Bool) (k : ℕ) :
    ∃ t v, t ≤ 5*k+2*w.length+1 ∧ value v = value w+k ∧
      machine.step^[t] (frame base .tick w k 1) = frame base .halt v 0 1 := by
  have hones : ∀ a : List Bool, ones a ≤ a.length := by
    intro a
    induction a with
    | nil => rfl
    | cons b a ih => cases b <;> simp [ones] at * <;> omega
  refine ⟨clock w k+1,increment^[k] w,?_,count_value w k,?_⟩
  · have := clock_potential w k
    have := hones w
    omega
  · rw [Function.iterate_succ_apply',count_run,tick_zero]

