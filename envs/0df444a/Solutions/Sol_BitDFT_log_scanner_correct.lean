-- Prove2me | solution 1 for BitDFT.log_scanner_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:09:44.060914+00:00
-- url     : https://prove2.me/submissions/9b4969b7-ba68-4244-8faf-db6c1dba1f2e

import Definitions.Def_BitDFT_LogScanner
import Theorems.Thm_BitDFT_guard_log_from_size
import Definitions.Def_BitDFT_BinaryCounter
import Mathlib.Tactic.Ring

namespace BitDFT.BinaryCounter

private theorem val_append_bit (w : List Bool) (b : Bool) :
    IntMul.val (w++[b]) = 2*IntMul.val w+b.toNat := by
  simp [IntMul.val,List.foldl_append]

private theorem value_reverse (w : List Bool) : value w.reverse = IntMul.val w := by
  suffices h : ∀ a : List Bool, value a = IntMul.val a.reverse by simpa using h w.reverse
  intro a
  induction a with
  | nil => rfl
  | cons b a ih =>
    rw [List.reverse_cons,val_append_bit]
    simp only [value,ih]
    omega

private theorem value_append (a b : List Bool) :
    value (a++b) = value a + 2^a.length*value b := by
  induction a with
  | nil => simp [value]
  | cons x a ih => simp [value,ih,pow_succ]; ring

private theorem value_zero (a : List Bool) : value a = 0 ↔ ∀ b ∈ a, b = false := by
  induction a with
  | nil => simp [value]
  | cons b a ih => cases b <;> simp [value,ih]

/-- On a canonical nonzero binary field, the power-of-two flag is exactly the
    assertion that every bit after the first one is zero. -/
theorem power_flag (tail : List Bool) :
    IntMul.val (true::tail) = 2^tail.length ↔ ∀ b ∈ tail, b = false := by
  rw [← value_reverse,List.reverse_cons,value_append]
  simp only [List.length_reverse,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  have hz : value tail.reverse = 0 ↔ ∀ b ∈ tail, b = false := by
    simpa using value_zero tail.reverse
  constructor
  · intro h
    apply hz.mp
    omega
  · intro h
    rw [hz.mpr h]
    simp


private theorem value_lt (a : List Bool) : value a < 2^a.length := by
  induction a with
  | nil => simp [value]
  | cons b a ih => cases b <;> simp [value,pow_succ] <;> omega

private theorem leading_one_value (tail : List Bool) :
    IntMul.val (true::tail) = value tail.reverse + 2^tail.length := by
  rw [← value_reverse,List.reverse_cons,value_append]
  simp [value]

theorem canonical_size (tail : List Bool) : (IntMul.val (true::tail)).size = tail.length+1 := by
  have hv : value tail.reverse < 2^tail.length := by simpa using value_lt tail.reverse
  have he := leading_one_value tail
  have hlo : 2^tail.length ≤ IntMul.val (true::tail) := by omega
  have hhi : IntMul.val (true::tail) < 2^(tail.length+1) := by rw [pow_succ]; omega
  have hslo := Nat.lt_size.mpr hlo
  have hshi := Nat.size_le.mpr hhi
  omega

theorem canonical_positive (tail : List Bool) : 1 ≤ IntMul.val (true::tail) := by
  have he := leading_one_value tail
  have hp : 0 < 2^tail.length := pow_pos (by decide) _
  omega

end BitDFT.BinaryCounter

namespace BitDFT.LogScanner
open IntMul

private theorem protect_stay (a : Sym) : HeaderReader.protect a (a,.stay) = (a,.stay) := by
  cases a <;> rfl

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem append_one (k : ℕ) :
    Function.update (machine.tapeOf (List.replicate k TapeCopy.Sym.one)) (k+1) TapeCopy.Sym.one =
      machine.tapeOf (List.replicate (k+1) TapeCopy.Sym.one) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    by_cases hp : p = k
    · subst p; simp [MultitapeTM.tapeOf]
    · rw [Function.update_of_ne (by omega : p+1 ≠ k+1)]
      simp only [MultitapeTM.tapeOf]
      by_cases hl : p < k
      · simp [hl,show p < k+1 by omega]
      · simp [hl,show ¬p < k+1 by omega]

private theorem emit_step (base : machine.Cfg) (q q' : State) (w : List Bool)
    (ip k : ℕ) (adv : Bool)
    (hr : raw q (fun i => (frame base q w ip k (k+1)).cells i ((frame base q w ip k (k+1)).head i)) =
      emit q' (fun i => (frame base q w ip k (k+1)).cells i ((frame base q w ip k (k+1)).head i)) adv)
    (h2 : (frame base q w ip k (k+1)).cells 2 ip ≠ TapeCopy.Sym.start) :
    machine.step (frame base q w ip k (k+1)) =
      frame base q' w (ip+adv.toNat) (k+1) (k+2) := by
  let c := frame base q w ip k (k+1)
  change raw c.state (fun i => c.cells i (c.head i)) = emit q' (fun i => c.cells i (c.head i)) adv at hr
  change c.cells 2 (c.head 2) ≠ TapeCopy.Sym.start at h2
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := by
    simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      emit q' (fun i => c.cells i (c.head i)) adv := by
    simp only [transition,hr]
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i
      · exact protect_stay _
      · exact protect_stay _
      · cases adv <;> simp [emit,HeaderReader.protect,h2]
      · simp [emit,h3,HeaderReader.protect]
  change machine.step c = _
  apply cfg_ext
  · simp [MultitapeTM.step,ht,emit,frame]
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i
    fin_cases i
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact Function.update_eq_self _ _
    · exact append_one k
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> cases adv <;> simp [emit,c,frame]

private theorem tape_nonstart (w : List Bool) (p : ℕ) :
    machine.tapeOf (w.map machine.bitSym) (p+1) ≠ TapeCopy.Sym.start := by
  simp only [MultitapeTM.tapeOf]
  by_cases h : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
    cases w[p] <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    decide

private theorem write2_step (base : machine.Cfg) (one : Bool) (w : List Bool) (p k : ℕ) :
    machine.step (frame base (.write2 one) w (p+1) k (k+1)) =
      frame base (.write1 one) w (p+1) (k+1) (k+2) := by
  exact emit_step base _ _ w (p+1) k false rfl (tape_nonstart w p)

private theorem write1_step (base : machine.Cfg) (one : Bool) (w : List Bool) (p k : ℕ) :
    machine.step (frame base (.write1 one) w (p+1) k (k+1)) =
      frame base (.scan true one) w (p+1) (k+1) (k+2) := by
  exact emit_step base _ _ w (p+1) k false rfl (tape_nonstart w p)

private theorem scan_step (base : machine.Cfg) (seen one b : Bool)
    (pre rest : List Bool) (k : ℕ) :
    machine.step (frame base (.scan seen one) (pre++b::rest) (pre.length+1) k (k+1)) =
      frame base (.write2 (one || b)) (pre++b::rest) (pre.length+2) (k+1) (k+2) := by
  refine emit_step base _ _ _ (pre.length+1) k true ?_ (tape_nonstart _ _)
  simp [raw,frame,MultitapeTM.tapeOf,MultitapeTM.bitSym]

private theorem scan_three (base : machine.Cfg) (seen one b : Bool)
    (pre rest : List Bool) (k : ℕ) :
    machine.step^[3] (frame base (.scan seen one) (pre++b::rest) (pre.length+1) k (k+1)) =
      frame base (.scan true (one || b)) (pre++b::rest) (pre.length+2) (k+3) (k+4) := by
  rw [show 3=2+1 by decide,Function.iterate_succ_apply,scan_step]
  rw [show 2=1+1 by decide,Function.iterate_succ_apply,write2_step]
  simpa using write1_step base (one || b) (pre++b::rest) (pre.length+1) (k+2)


private theorem pad_step (base : machine.Cfg) (w : List Bool) (p k j : ℕ) (hj : j+1 < 9) :
    machine.step (frame base (.pad ⟨j+1,hj⟩) w (p+1) k (k+1)) =
      frame base (.pad ⟨j,by omega⟩) w (p+1) (k+1) (k+2) := by
  exact emit_step base _ _ w (p+1) k false (by simp [raw]) (tape_nonstart w p)

private theorem pad_zero (base : machine.Cfg) (w : List Bool) (ip k : ℕ) :
    machine.step (frame base (.pad 0) w ip k (k+1)) = frame base .halt w ip k k := by
  let c := frame base (.pad 0) w ip k (k+1)
  have h3 : c.cells 3 (c.head 3) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.halt,fun i => (c.cells i (c.head i),if i = 3 then Move.left else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i = 3
      · subst i; simp [transition,raw,show c.state = State.pad 0 from rfl,h3,HeaderReader.protect]
      · simp [transition,raw,show c.state = State.pad 0 from rfl,hi,protect_stay]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i; exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i; fin_cases i <;> simp [c,frame]

private theorem pad_run (base : machine.Cfg) (w : List Bool) (p k j : ℕ) (hj : j < 9) :
    machine.step^[j+1] (frame base (.pad ⟨j,hj⟩) w (p+1) k (k+1)) =
      frame base .halt w (p+1) (k+j) (k+j) := by
  induction j generalizing k with
  | zero => simpa using pad_zero base w (p+1) k
  | succ j ih =>
    rw [Function.iterate_succ_apply,pad_step]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1) (by omega)

private theorem scan_end (base : machine.Cfg) (w : List Bool) (seen one : Bool) (k : ℕ) :
    machine.step (frame base (.scan seen one) w (w.length+1) k (k+1)) =
      frame base (.pad (extra seen one)) w (w.length+1) k (k+1) := by
  let c := frame base (.scan seen one) w (w.length+1) k (k+1)
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.blank := by simp [c,frame,MultitapeTM.tapeOf]
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.pad (extra seen one),fun i => (c.cells i (c.head i),Move.stay)) := by
    apply Prod.ext
    · simp [transition,raw,show c.state = State.scan seen one from rfl,h2]
    · funext i; simp [transition,raw,show c.state = State.scan seen one from rfl,h2,protect_stay]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i; exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]; rfl

private theorem start_step (base : machine.Cfg) (tail : List Bool) :
    machine.step (frame base .start (true::tail) 1 0 1) =
      frame base (.scan false false) (true::tail) 2 0 1 := by
  let c := frame base .start (true::tail) 1 0 1
  have h2 : c.cells 2 (c.head 2) = TapeCopy.Sym.one := rfl
  have ht : transition c.state (fun i => c.cells i (c.head i)) =
      (.scan false false,fun i => (c.cells i (c.head i),if i = 2 then Move.right else Move.stay)) := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i = 2
      · subst i; simp [transition,raw,show c.state = State.start from rfl,h2,HeaderReader.protect]
      · simp [transition,raw,show c.state = State.start from rfl,hi,protect_stay]
  change machine.step c = _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · change (fun i => Function.update (c.cells i) (c.head i) ((transition c.state _).2 i).1) = _
    rw [ht]
    funext i; exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i; fin_cases i <;> rfl

private theorem scan_loop (base : machine.Cfg) (pre rest : List Bool) (seen one : Bool) (k : ℕ) :
    machine.step^[3*rest.length]
      (frame base (.scan seen one) (pre++rest) (pre.length+1) k (k+1)) =
    frame base (.scan (seen || !rest.isEmpty) (rest.foldl Bool.or one))
      (pre++rest) (pre.length+rest.length+1) (k+3*rest.length) (k+3*rest.length+1) := by
  induction rest generalizing pre seen one k with
  | nil => simp
  | cons b rest ih =>
    rw [List.length_cons,show 3*(rest.length+1)=3*rest.length+3 by omega,
      Function.iterate_add_apply,scan_three]
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using
      ih (pre++[b]) true (one || b) (k+3)

private theorem fold_or (w : List Bool) (b : Bool) : w.foldl Bool.or b = (b || w.any id) := by
  induction w generalizing b with
  | nil => simp
  | cons x w ih => simp [ih,Bool.or_assoc]

def incrementCount (tail : List Bool) : ℕ :=
  3*tail.length + (extra (!tail.isEmpty) (tail.any id)).val

/-- This scanner leaves the exact unary increment and parks its head on the final mark. -/
theorem scanner_run (base : machine.Cfg) (tail : List Bool) :
    machine.step^[incrementCount tail+3] (frame base .start (true::tail) 1 0 1) =
      frame base .halt (true::tail) (tail.length+2) (incrementCount tail) (incrementCount tail) := by
  let j := extra (!tail.isEmpty) (tail.any id)
  have hs : machine.step^[3*tail.length] (frame base (.scan false false) (true::tail) 2 0 1) =
      frame base (.scan (!tail.isEmpty) (tail.any id)) (true::tail) (tail.length+2)
        (3*tail.length) (3*tail.length+1) := by
    simpa [fold_or,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      scan_loop base [true] tail false false 0
  rw [show incrementCount tail+3 = ((j.val+2)+3*tail.length)+1 by
    simp [incrementCount,j]; omega,Function.iterate_succ_apply,start_step,
    Function.iterate_add_apply,hs]
  rw [show j.val+2=(j.val+1)+1 by omega,Function.iterate_succ_apply]
  have he := scan_end base (true::tail) (!tail.isEmpty) (tail.any id) (3*tail.length)
  simp only [List.length_cons] at he
  rw [he]
  exact pad_run base (true::tail) (tail.length+1) (3*tail.length) j.val j.isLt


theorem count_eq_log (tail : List Bool) :
    incrementCount tail = 3*IntMul.lg (IntMul.val (true::tail))+5 := by
  cases tail with
  | nil => simp [incrementCount,extra,IntMul.val,IntMul.lg]
  | cons b rest =>
    let w := b::rest
    have hs := BinaryCounter.canonical_size w
    have hl := BitDFT.guard_log_from_size (IntMul.val (true::w)) (BinaryCounter.canonical_positive w)
    rw [hs] at hl
    simp only [Nat.add_sub_cancel] at hl
    have hwlen : 1 ≤ w.length := by simp [w]
    cases ho : w.any id with
    | false =>
      have hz : ∀ x ∈ w, x = false := by simpa using List.any_eq_false.mp ho
      have hp := (BinaryCounter.power_flag w).mpr hz
      rw [if_pos hp, max_eq_left hwlen] at hl
      change incrementCount w = _
      rw [hl]
      simp [incrementCount,extra,ho,w]
    | true =>
      have hp : IntMul.val (true::w) ≠ 2^w.length := by
        intro he
        have hz := (BinaryCounter.power_flag w).mp he
        have hfalse : w.any id = false := List.any_eq_false.mpr (by simpa using hz)
        rw [ho] at hfalse
        cases hfalse
      rw [if_neg hp, max_eq_left (by omega : 1 ≤ w.length+1)] at hl
      change incrementCount w = _
      rw [hl]
      simp [incrementCount,extra,ho,w]
      omega

end BitDFT.LogScanner

open BitDFT.LogScanner IntMul

/-- A genuine finite scan prepares the logarithmic unary increment, with its exact clock. -/
theorem solution (base : machine.Cfg) (tail : List Bool) :
    let k := 3*IntMul.lg (IntMul.val (true::tail))+5
    machine.step^[k+3] (frame base .start (true::tail) 1 0 1) =
      frame base .halt (true::tail) (tail.length+2) k k := by
  dsimp only
  rw [← count_eq_log]
  exact scanner_run base tail

