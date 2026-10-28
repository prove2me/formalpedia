-- Prove2me | solution 1 for BitDFT.counted_block_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T17:54:18.044873+00:00
-- url     : https://prove2.me/submissions/8a569262-b3c6-4c34-b5c9-cdc6da842988

import Definitions.Def_BitDFT_CountedBlock
import Theorems.Thm_IntMul_CountedStream_template_reset_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic


namespace IntMul.BinaryAdder

private theorem full_adder_value (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

private theorem add_little_length (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    (addLittle x y c).length = x.length + 1 := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => rfl
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, List.length_cons, ih ys _ ht]

private theorem add_little_value (x y : List Bool) (c : Bool) (h : x.length = y.length) :
    littleVal (addLittle x y c) = littleVal x + littleVal y + c.toNat := by
  induction x generalizing y c with
  | nil =>
      cases y with
      | nil => simp [addLittle, littleVal]
      | cons b ys => simp at h
  | cons a xs ih =>
      cases y with
      | nil => simp at h
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using h
          simp only [addLittle, littleVal, ih ys _ ht]
          have hv := full_adder_value a b c
          omega

private theorem little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2 * acc + b.toNat) a = 2 ^ x.length * a + IntMul.val x := by
  induction x generalizing a with
  | nil => simp [IntMul.val]
  | cons b xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      have hv : IntMul.val (b :: xs) = 2 ^ xs.length * b.toNat + IntMul.val xs := by
        simp only [IntMul.val, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
        exact ih b.toNat
      rw [hv, pow_succ]
      ring

private theorem val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact foldl_affine y _

private theorem val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, val_append, val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring

/-- Ripple-carry addition computes the ordinary campaign-model value, preserving
all leading zeroes and adding exactly one final carry position. -/
private theorem ripple_sum_spec (x y : List Bool) (h : x.length = y.length) :
    ((addLittle x.reverse y.reverse false).reverse).length = x.length + 1 ∧
    IntMul.val ((addLittle x.reverse y.reverse false).reverse) = IntMul.val x + IntMul.val y := by
  have hl : x.reverse.length = y.reverse.length := by simpa using h
  constructor
  · simpa using add_little_length x.reverse y.reverse false hl
  · rw [val_reverse_little, add_little_value _ _ _ hl]
    have hx : littleVal x.reverse = IntMul.val x := by
      rw [← val_reverse_little, List.reverse_reverse]
    have hy : littleVal y.reverse = IntMul.val y := by
      rw [← val_reverse_little, List.reverse_reverse]
    simp [hx, hy]

/-- Every little-endian word has exactly its specified binary digits, including
trailing zeroes; no normalization assumption is needed. -/
private theorem little_value_test_bit (x : List Bool) (i : ℕ) :
    (littleVal x).testBit i = x.getD i false := by
  induction x generalizing i with
  | nil => simp [littleVal]
  | cons b xs ih =>
      have hv : littleVal (b :: xs) = Nat.bit b (littleVal xs) := by
        cases b <;> simp [littleVal, Nat.bit] <;> omega
      rw [hv]
      cases i with
      | zero => cases b <;> simp [Nat.bit, Nat.testBit_zero]
      | succ i => rw [Nat.testBit_bit_succ]; simpa using ih i

/-- The campaign's padded big-endian binary encoding returns every original
word, preserving its declared width and any leading zeroes. -/
private theorem bin_value_roundtrip (x : List Bool) : IntMul.bin x.length (IntMul.val x) = x := by
  have hv : IntMul.val x = littleVal x.reverse := by
    rw [← val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]

/-- The ripple adder produces exactly the canonical output word demanded by the
linear-time addition milestone, rather than merely a word of the same value. -/
private theorem ripple_sum_bin (x y : List Bool) (h : x.length = y.length) :
    (addLittle x.reverse y.reverse false).reverse =
      IntMul.bin (x.length + 1) (IntMul.val x + IntMul.val y) := by
  have hs := ripple_sum_spec x y h
  have hr := bin_value_roundtrip ((addLittle x.reverse y.reverse false).reverse)
  rw [hs.1, hs.2] at hr
  exact hr.symm

end IntMul.BinaryAdder




/-! Decrement arithmetic adapted from the frozen public CounterArithmetic
module, with Boolean direction fixed to decrement and the campaign word value.
The integrated controller and actual campaign-machine trace are separate. -/
namespace IntMul.CountedStream

open IntMul.BinaryAdder (littleVal)

private theorem updated_nil : updated [] = [] := rfl

private theorem updated_zero (bs : List Bool) : updated (false :: bs) = true :: updated bs := by
  simp [updated, carryLength, stopTail, List.replicate_succ]

private theorem updated_one (bs : List Bool) : updated (true :: bs) = false :: bs := by
  simp [updated, carryLength, stopTail]

private theorem updated_length (bits : List Bool) : (updated bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · rw [updated_zero]; simp [ih]
      · rw [updated_one]; rfl

private theorem carry_length_le (bits : List Bool) : carryLength bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [carryLength, List.length_cons]; split_ifs <;> omega

private theorem potential_le (bits : List Bool) : potential bits ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [potential, List.length_cons]; split_ifs <;> omega

private theorem potential_accounting (bits : List Bool) :
    carryLength bits + potential (updated bits) ≤ potential bits + 1 := by
  induction bits with
  | nil => simp [carryLength, potential, updated_nil]
  | cons b bs ih =>
      cases b
      · rw [updated_zero]
        simp only [carryLength, potential, if_true, Bool.true_eq_false, if_false]
        omega
      · rw [updated_one]
        simp [carryLength, potential, Nat.add_comm]

private theorem amortized_step (bits : List Bool) :
    counterSteps bits + 2 * potential (updated bits) ≤ 4 + 2 * potential bits := by
  have h := potential_accounting bits
  unfold counterSteps
  omega

private theorem iterate_counter_length (n : ℕ) (bits : List Bool) :
    (iterateCounter n bits).length = bits.length := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => rw [iterateCounter, ih, updated_length]

private theorem amortized_total (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits + 2 * potential (iterateCounter n bits) ≤ 4 * n + 2 * potential bits := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      have h := amortized_step bits
      have hn := ih (updated bits)
      simp only [totalCounterSteps, iterateCounter]
      omega

private theorem total_counter_steps_bound (n : ℕ) (bits : List Bool) :
    totalCounterSteps n bits ≤ 4 * n + 2 * bits.length := by
  have h := amortized_total n bits
  have hp := potential_le bits
  omega

/-- Exact decrement, including the fixed-width wrap term on underflow. -/
private theorem decrement_value (bits : List Bool) :
    value bits + (if underflow bits then 2 ^ bits.length else 0) = value (updated bits) + 1 := by
  induction bits with
  | nil => simp [updated_nil, value, littleVal, underflow]
  | cons b bs ih =>
      simp only [value] at ih
      cases b
      · rw [updated_zero]
        simp only [value, littleVal, underflow, Bool.toNat_false, Bool.toNat_true,
          if_true, List.length_cons, pow_succ]
        cases ho : underflow bs <;> simp [ho] at ih ⊢ <;> omega
      · simp [updated_one, value, littleVal, underflow, Nat.add_comm]

private theorem underflow_iff_zero (bits : List Bool) : underflow bits = true ↔ value bits = 0 := by
  induction bits with
  | nil => simp [underflow, value, littleVal]
  | cons b bs ih => cases b <;> simp [underflow, value, littleVal, ih]

private theorem underflow_all_ones (bits : List Bool) (h : underflow bits = true) :
    updated bits = List.replicate bits.length true := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      cases b
      · rw [updated_zero]
        simp only [underflow, if_true] at h
        rw [ih h, List.length_cons, List.replicate_succ]
      · simp [underflow] at h

private theorem decrement_positive (bits : List Bool) (h : 0 < value bits) :
    underflow bits = false ∧ value (updated bits) + 1 = value bits := by
  have hn : underflow bits ≠ true := by
    intro hflag
    have := (underflow_iff_zero bits).mp hflag
    omega
  have hf : underflow bits = false := by cases hflag : underflow bits <;> simp_all
  refine ⟨hf, ?_⟩
  have hv := decrement_value bits
  simpa [hf] using hv.symm

private theorem countdown_value (bits : List Bool) (n : ℕ) (hn : n ≤ value bits) :
    value (iterateCounter n bits) = value bits - n := by
  induction n generalizing bits with
  | zero => simp [iterateCounter]
  | succ n ih =>
      have hp : 0 < value bits := by omega
      have hv := (decrement_positive bits hp).2
      have hnext : n ≤ value (updated bits) := by omega
      rw [iterateCounter, ih (updated bits) hnext]
      omega

private theorem countdown_not_finished (bits : List Bool) (n : ℕ) (hn : n < value bits) :
    underflow (iterateCounter n bits) = false := by
  have hv := countdown_value bits n hn.le
  exact (decrement_positive _ (by omega)).1

private theorem countdown_final_underflow (bits : List Bool) :
    underflow (iterateCounter (value bits) bits) = true := by
  apply (underflow_iff_zero _).mpr
  rw [countdown_value bits (value bits) le_rfl]
  omega


private theorem total_counter_steps_succ (n : ℕ) (bits : List Bool) :
    totalCounterSteps (n + 1) bits = totalCounterSteps n bits + counterSteps (iterateCounter n bits) := by
  induction n generalizing bits with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      change counterSteps bits + totalCounterSteps (n + 1) (updated bits) =
        (counterSteps bits + totalCounterSteps n (updated bits)) + counterSteps (iterateCounter n (updated bits))
      rw [ih (updated bits)]
      omega

end IntMul.CountedStream



namespace IntMul.CountedStream

open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)

/-- A tape write can replace the first symbol after a fixed prefix without
disturbing the suffix. This is the physical write used by reverse ripple addition. -/
private theorem counter_tape_replace_after_prefix (M : MultitapeTM)
    (pre post : List M.Sym) (old new : M.Sym) :
    Function.update (M.tapeOf (pre ++ old :: post)) (pre.length + 1) new =
      M.tapeOf (pre ++ new :: post) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases he : p = pre.length
      · subst p
        simp [MultitapeTM.tapeOf, List.getD_append_right]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ pre.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hl : p < pre.length
        · rw [List.getD_append _ _ _ _ hl, List.getD_append _ _ _ _ hl]
        · have hge : pre.length ≤ p := by omega
          rw [List.getD_append_right _ _ _ _ hge, List.getD_append_right _ _ _ _ hge]
          cases hd : p - pre.length with
          | zero => omega
          | succ d => simp

private theorem counter_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem counter_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]



private theorem counter_safe_left (s : Sym) (h : s ≠ .start) : safeStep s s .left = (s, .left) := by
  simp [safeStep, h]

private theorem counter_carry_zero_transition (a : Fin 4 → Sym) (h : a 2 = .zero) :
    transition .carry a = (.carry, fun i =>
      (if i = 2 then .one else a i, if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, h, if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi, safe_stay]

private theorem counter_carry_one_transition (a : Fin 4 → Sym) (h : a 2 = .one) :
    transition .carry a = (.rewind false, fun i =>
      (if i = 2 then .zero else a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.one = Sym.zero)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    decide
  · simp only [if_neg hi, safe_stay]

private theorem counter_carry_sep_transition (a : Fin 4 → Sym) (h : a 2 = .sep) :
    transition .carry a = (.rewind true, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬Sym.sep = Sym.zero),
    if_neg (by decide : ¬Sym.sep = Sym.one)]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, counter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem counter_rewind_bit_transition (a : Fin 4 → Sym) (f : Bool)
    (h : a 2 = .zero ∨ a 2 = .one) :
    transition (.rewind f) a = (.rewind f, fun i => (a i, if i = 2 then .right else .stay)) := by
  simp only [transition, rawTransition, if_pos h]
  congr 1
  funext i
  by_cases hi : i = 2
  · simp only [if_pos hi, counter_safe_right]
  · simp only [if_neg hi, safe_stay]

private theorem counter_rewind_sep_transition (a : Fin 4 → Sym) (f : Bool) (h : a 2 = .sep) :
    transition (.rewind f) a = (.done f, fun i => (a i, if i = 2 then .left else .stay)) := by
  simp only [transition, rawTransition, h]
  rw [if_neg (by decide : ¬(Sym.sep = Sym.zero ∨ Sym.sep = Sym.one))]
  simp only [if_true]
  congr 1
  funext i
  by_cases hi : i = 2
  · subst i
    simp only [if_pos rfl]
    rw [h]
    exact counter_safe_left _ (by decide)
  · simp only [if_neg hi, safe_stay]

private theorem counter_bit_mem (b : Bool) : machine.bitSym b = Sym.zero ∨ machine.bitSym b = Sym.one := by
  cases b <;> decide

/-- Reading the least significant remaining bit after the left delimiter. -/
private theorem counter_reverse_last (b : Bool) (bs done : List Bool) :
    (((b :: bs).reverse ++ done).map machine.bitSym).getD bs.length machine.blank = machine.bitSym b := by
  simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.map_append, List.map_cons]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem counter_carry_read (base : machine.Cfg) (b : Bool) (bs done : List Bool) :
    (carryFrame base (b :: bs) done).cells 2 ((carryFrame base (b :: bs) done).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: (((b :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
    (bs.length + 2) = machine.bitSym b
  rw [show bs.length + 2 = (bs.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  exact counter_reverse_last b bs done

private theorem counter_carry_zero_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (false :: bs) done) = carryFrame base bs (true :: done) := by
  have hz : (carryFrame base (false :: bs) done).cells 2
      ((carryFrame base (false :: bs) done).head 2) = Sym.zero := counter_carry_read base false bs done
  have ht := counter_carry_zero_transition
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) hz
  change transition (carryFrame base (false :: bs) done).state
    (fun i => (carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _ at ht
  apply counter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      change Function.update
        (machine.tapeOf (Sym.sep :: (((false :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (bs.length + 2) Sym.one =
          machine.tapeOf (Sym.sep :: ((bs.reverse ++ true :: done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse,
        List.map_nil, List.nil_append, MultitapeTM.bitSym, Bool.false_eq_true, if_false, if_true] using
        counter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) Sym.zero Sym.one
    · simp only [if_neg hi]
      change Function.update ((carryFrame base (false :: bs) done).cells i)
        ((carryFrame base (false :: bs) done).head i)
        ((carryFrame base (false :: bs) done).cells i ((carryFrame base (false :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [carryFrame, hi]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      simp [carryFrame]
    · simp [carryFrame, hi]


private theorem counter_carry_one_step (base : machine.Cfg) (bs done : List Bool) :
    machine.step (carryFrame base (true :: bs) done) = rewindFrame base false (false :: bs).reverse done := by
  have ho : (carryFrame base (true :: bs) done).cells 2
      ((carryFrame base (true :: bs) done).head 2) = Sym.one := counter_carry_read base true bs done
  have ht := counter_carry_one_transition
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) ho
  change transition (carryFrame base (true :: bs) done).state
    (fun i => (carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _ at ht
  apply counter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      change Function.update
        (machine.tapeOf (Sym.sep :: (((true :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep])))
        (bs.length + 2) Sym.zero =
          machine.tapeOf (Sym.sep :: (((false :: bs).reverse ++ done).map machine.bitSym ++ [Sym.sep]))
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_append, List.map_cons, List.map_singleton, List.cons_append,
        List.length_cons, List.length_map, List.length_reverse,
        List.map_nil, List.nil_append, MultitapeTM.bitSym, Bool.false_eq_true, if_false, if_true] using
        counter_tape_replace_after_prefix machine (Sym.sep :: bs.reverse.map machine.bitSym)
          (done.map machine.bitSym ++ [Sym.sep]) Sym.one Sym.zero
    · simp only [if_neg hi]
      change Function.update ((carryFrame base (true :: bs) done).cells i)
        ((carryFrame base (true :: bs) done).head i)
        ((carryFrame base (true :: bs) done).cells i ((carryFrame base (true :: bs) done).head i)) = _
      rw [Function.update_eq_self]
      simp [carryFrame, rewindFrame, hi]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2
    · subst i
      simp [carryFrame, rewindFrame]
    · simp [carryFrame, rewindFrame, hi]

private theorem counter_carry_nil_step (base : machine.Cfg) (done : List Bool) :
    machine.step (carryFrame base [] done) = rewindFrame base true [] done := by
  have hm : (carryFrame base [] done).cells 2 ((carryFrame base [] done).head 2) = Sym.sep := rfl
  have ht := counter_carry_sep_transition
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) hm
  change transition (carryFrame base [] done).state
    (fun i => (carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _ at ht
  apply counter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((carryFrame base [] done).cells i) ((carryFrame base [] done).head i)
      ((carryFrame base [] done).cells i ((carryFrame base [] done).head i)) = _
    rw [Function.update_eq_self]
    simp [carryFrame, rewindFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [carryFrame, rewindFrame, hi]

private theorem counter_rewind_read (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = machine.bitSym b := by
  change (machine.tapeOf (Sym.sep :: ((pre ++ b :: bs).map machine.bitSym ++ [Sym.sep])))
    (pre.length + 2) = machine.bitSym b
  rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
  simp only [MultitapeTM.tapeOf, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.map_append, List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem counter_rewind_step (base : machine.Cfg) (f b : Bool) (pre bs : List Bool) :
    machine.step (rewindFrame base f pre (b :: bs)) = rewindFrame base f (pre ++ [b]) bs := by
  have hb : (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.zero ∨
      (rewindFrame base f pre (b :: bs)).cells 2 ((rewindFrame base f pre (b :: bs)).head 2) = Sym.one := by
    rw [counter_rewind_read]
    exact counter_bit_mem b
  have ht := counter_rewind_bit_transition
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) f hb
  change transition (rewindFrame base f pre (b :: bs)).state
    (fun i => (rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _ at ht
  apply counter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame base f pre (b :: bs)).cells i) ((rewindFrame base f pre (b :: bs)).head i)
      ((rewindFrame base f pre (b :: bs)).cells i ((rewindFrame base f pre (b :: bs)).head i)) = _
    rw [Function.update_eq_self]
    simp [rewindFrame, List.append_assoc]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [rewindFrame, hi]

private theorem counter_rewind_end (base : machine.Cfg) (f : Bool) (pre : List Bool) :
    machine.step (rewindFrame base f pre []) = counterFrame base (.done f) pre.reverse := by
  have hs : (rewindFrame base f pre []).cells 2 ((rewindFrame base f pre []).head 2) = Sym.sep := by
    change (machine.tapeOf (Sym.sep :: ((pre ++ []).map machine.bitSym ++ [Sym.sep])))
      (pre.length + 2) = Sym.sep
    rw [show pre.length + 2 = (pre.length + 1) + 1 by omega]
    simp only [MultitapeTM.tapeOf, List.getD_cons_succ, List.append_nil]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have ht := counter_rewind_sep_transition
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) f hs
  change transition (rewindFrame base f pre []).state
    (fun i => (rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _ at ht
  apply counter_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((rewindFrame base f pre []).cells i) ((rewindFrame base f pre []).head i)
      ((rewindFrame base f pre []).cells i ((rewindFrame base f pre []).head i)) = _
    rw [Function.update_eq_self]
    simp [rewindFrame, counterFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    by_cases hi : i = 2 <;> simp [rewindFrame, counterFrame, hi]

private theorem counter_rewind_run (base : machine.Cfg) (f : Bool) (pre right : List Bool) :
    machine.step^[right.length + 1] (rewindFrame base f pre right) =
      counterFrame base (.done f) (pre ++ right).reverse := by
  induction right generalizing pre with
  | nil => simpa using counter_rewind_end base f pre
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp,
        Function.iterate_succ_apply, counter_rewind_step, ih]
      simp [List.append_assoc]

private theorem counter_carry_run (base : machine.Cfg) (bits done : List Bool) :
    machine.step^[carryLength bits + 1] (carryFrame base bits done) =
      rewindFrame base (underflow bits) (stopTail bits).reverse
        (List.replicate (carryLength bits) true ++ done) := by
  induction bits generalizing done with
  | nil => simpa [carryLength, underflow, stopTail] using counter_carry_nil_step base done
  | cons b bs ih =>
      cases b
      · simp only [carryLength, underflow, stopTail, if_true]
        rw [Function.iterate_succ_apply, counter_carry_zero_step, ih]
        simp [List.replicate_succ', List.append_assoc]
      · simpa [carryLength, underflow, stopTail] using counter_carry_one_step base bs done

/-- The actual decrement table restores the head and preserves all other tapes.
Its exact count includes propagation, resolution, and the full head return. -/
private theorem counter_correct (base : machine.Cfg) (bits : List Bool) :
    machine.step^[counterSteps bits] (counterFrame base .carry bits) =
      counterFrame base (.done (underflow bits)) (updated bits) := by
  have hc : counterFrame base .carry bits = carryFrame base bits [] := by
    apply counter_cfg_ext <;> simp [counterFrame, carryFrame]
  have ht : counterSteps bits = (carryLength bits + 1) + (carryLength bits + 1) := by
    unfold counterSteps
    omega
  rw [hc, ht, Function.iterate_add_apply, counter_carry_run]
  simp only [List.append_nil]
  have hr := counter_rewind_run base (underflow bits) (stopTail bits).reverse (List.replicate (carryLength bits) true)
  simpa [updated, List.reverse_append, List.reverse_replicate] using hr

end IntMul.CountedStream




namespace IntMul.CountedStream
open IntMul.TapeCopy (Sym)
open IntMul.TapeAdder (safeStep safe_stay)
private abbrev streamFrame := BitDFT.CountedBlock.frame

private theorem controller_cfg_ext (c d : machine.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem controller_safe_right (s : Sym) : safeStep s s .right = (s, .right) := by
  by_cases hs : s = .start <;> simp [safeStep, hs]

private theorem controller_tapeOf_append_one (M : MultitapeTM) (w : List M.Sym) (a : M.Sym) :
    Function.update (M.tapeOf w) (w.length + 1) a = M.tapeOf (w ++ [a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p = w.length
      · subst p
        simp [MultitapeTM.tapeOf]
      · rw [Function.update_of_ne (by omega : p + 1 ≠ w.length + 1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p < w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length ≤ p := by omega
          rw [List.getD_eq_default _ _ hge, List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp; omega)).symm

private theorem controller_counter_frame_from_stream (pre out x y old bits : List Bool) (j : ℕ) (q₀ q : State)
    (h : bits.length = y.length) :
    counterFrame (streamFrame pre out x y old j q₀) q bits = streamFrame pre out x y bits j q := by
  apply controller_cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame, BitDFT.CountedBlock.frame]
  · funext i
    fin_cases i <;> simp [counterFrame, streamFrame, BitDFT.CountedBlock.frame, h]

private theorem controller_stream_counter (pre out x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step^[counterSteps bits] (streamFrame pre out x y bits j .carry) =
      streamFrame pre out x y (updated bits) j (.done (underflow bits)) := by
  have hf := controller_counter_frame_from_stream pre out x y bits bits j .carry .carry h
  rw [← hf, counter_correct]
  exact controller_counter_frame_from_stream pre out x y bits (updated bits) j .carry (.done (underflow bits))
    (by rw [updated_length]; exact h)

private theorem controller_emit_transition (a : Fin 4 → Sym) (b : Bool)
    (hb : a 0 = machine.bitSym b) (ho : a 1 = .blank) :
    transition .emit a = (.carry, fun i =>
      (if i = 1 then machine.bitSym b else a i, if i = 0 ∨ i = 1 then .right else .stay)) := by
  have hbit : a 0 = Sym.zero ∨ a 0 = Sym.one := by rw [hb]; cases b <;> decide
  simp only [transition, rawTransition, if_pos hbit]
  congr 1
  funext i
  fin_cases i
  · change safeStep (a 0) (a 0) .right = (a 0, .right)
    exact controller_safe_right _
  · change safeStep (a 1) (a 0) .right = (machine.bitSym b, .right)
    rw [ho, hb]
    cases b <;> decide
  · exact safe_stay _
  · exact safe_stay _

private theorem controller_emit_step (pre out x y bits : List Bool) (j : ℕ) (hj : j < x.length) :
    machine.step (streamFrame pre out x y bits j .emit) = streamFrame pre out x y bits (j+1) .carry := by
  have hl : ((out++x.take j).map machine.bitSym).length = out.length+j := by
    simp [Nat.min_eq_left hj.le]
  have hr : (streamFrame pre out x y bits j .emit).cells 0
      ((streamFrame pre out x y bits j .emit).head 0) = machine.bitSym x[j] := by
    change ((pre++x).map machine.bitSym).getD (pre.length+j) machine.blank = _
    rw [List.map_append,List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_map,Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have ho : (streamFrame pre out x y bits j .emit).cells 1
      ((streamFrame pre out x y bits j .emit).head 1) = Sym.blank := by
    change ((out++x.take j).map machine.bitSym).getD (out.length+j) machine.blank = _
    exact List.getD_eq_default _ _ hl.le
  have ht := controller_emit_transition
    (fun i => (streamFrame pre out x y bits j .emit).cells i ((streamFrame pre out x y bits j .emit).head i)) x[j] hr ho
  change transition (streamFrame pre out x y bits j .emit).state
    (fun i => (streamFrame pre out x y bits j .emit).cells i ((streamFrame pre out x y bits j .emit).head i)) = _ at ht
  apply controller_cfg_ext
  · simp only [MultitapeTM.step,ht]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · change Function.update ((streamFrame pre out x y bits j .emit).cells 0)
        ((streamFrame pre out x y bits j .emit).head 0)
        ((streamFrame pre out x y bits j .emit).cells 0 ((streamFrame pre out x y bits j .emit).head 0)) = _
      rw [Function.update_eq_self]; rfl
    · change Function.update (machine.tapeOf ((out++x.take j).map machine.bitSym)) (out.length+j+1)
        (machine.bitSym x[j]) = machine.tapeOf ((out++x.take (j+1)).map machine.bitSym)
      have hnew : (out++x.take (j+1)).map machine.bitSym =
          (out++x.take j).map machine.bitSym++[machine.bitSym x[j]] := by
        rw [List.take_succ_eq_append_getElem hj,← List.append_assoc,List.map_append]
        rfl
      rw [hnew]
      have hw := controller_tapeOf_append_one machine ((out++x.take j).map machine.bitSym) (machine.bitSym x[j])
      rw [hl] at hw
      exact hw
    all_goals
      change Function.update ((streamFrame pre out x y bits j .emit).cells _) ((streamFrame pre out x y bits j .emit).head _)
        ((streamFrame pre out x y bits j .emit).cells _ ((streamFrame pre out x y bits j .emit).head _)) = _
      rw [Function.update_eq_self]; rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [streamFrame,BitDFT.CountedBlock.frame,Nat.add_assoc]

private theorem controller_done_transition (a : Fin 4 → Sym) (f : Bool) :
    transition (.done f) a = (if f then .resetLeft else .emit, fun i => (a i, .stay)) := by
  simp [transition, rawTransition, safe_stay]

private theorem controller_done_false_step (pre out x y bits : List Bool) (j : ℕ) :
    machine.step (streamFrame pre out x y bits j (.done false)) = streamFrame pre out x y bits j .emit := by
  have ht := controller_done_transition (fun i => (streamFrame pre out x y bits j (.done false)).cells i
    ((streamFrame pre out x y bits j (.done false)).head i)) false
  change transition (streamFrame pre out x y bits j (.done false)).state
    (fun i => (streamFrame pre out x y bits j (.done false)).cells i
      ((streamFrame pre out x y bits j (.done false)).head i)) = _ at ht
  apply controller_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((streamFrame pre out x y bits j (.done false)).cells i)
      ((streamFrame pre out x y bits j (.done false)).head i)
      ((streamFrame pre out x y bits j (.done false)).cells i ((streamFrame pre out x y bits j (.done false)).head i)) = _
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step, ht]
    rfl

private theorem controller_done_true_step (pre out x y bits : List Bool) (j : ℕ) (h : bits.length = y.length) :
    machine.step (streamFrame pre out x y bits j (.done true)) =
      resetFrame (streamFrame pre out x y bits j (.done true)) .resetLeft bits.reverse y (y.length + 1) := by
  have ht := controller_done_transition (fun i => (streamFrame pre out x y bits j (.done true)).cells i
    ((streamFrame pre out x y bits j (.done true)).head i)) true
  change transition (streamFrame pre out x y bits j (.done true)).state
    (fun i => (streamFrame pre out x y bits j (.done true)).cells i
      ((streamFrame pre out x y bits j (.done true)).head i)) = _ at ht
  apply controller_cfg_ext
  · simp only [MultitapeTM.step, ht]
    rfl
  · simp only [MultitapeTM.step, ht]
    funext i
    change Function.update ((streamFrame pre out x y bits j (.done true)).cells i)
      ((streamFrame pre out x y bits j (.done true)).head i)
      ((streamFrame pre out x y bits j (.done true)).cells i ((streamFrame pre out x y bits j (.done true)).head i)) = _
    rw [Function.update_eq_self]
    fin_cases i <;> simp [streamFrame, BitDFT.CountedBlock.frame, resetFrame]
  · simp only [MultitapeTM.step, ht]
    funext i
    fin_cases i <;> simp [streamFrame, BitDFT.CountedBlock.frame, resetFrame]


private theorem controller_nonterminal_cycle (pre out x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hp : 0 < value bits) :
    machine.step^[counterSteps bits + 2] (streamFrame pre out x y bits j .emit) =
      streamFrame pre out x y (updated bits) (j + 1) .emit := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, controller_emit_step pre out x y bits j hj,
    Function.iterate_succ_apply', controller_stream_counter pre out x y bits (j + 1) hw,
    (decrement_positive bits hp).1, controller_done_false_step]

private theorem controller_loop_run (pre out x y : List Bool) (n : ℕ) (bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hv : n ≤ value bits) (hx : j + n ≤ x.length) :
    machine.step^[2 * n + totalCounterSteps n bits] (streamFrame pre out x y bits j .emit) =
      streamFrame pre out x y (iterateCounter n bits) (j + n) .emit := by
  induction n generalizing bits j with
  | zero => simp [totalCounterSteps, iterateCounter]
  | succ n ih =>
      have hp : 0 < value bits := by omega
      have hval := (decrement_positive bits hp).2
      have htime : 2 * (n + 1) + totalCounterSteps (n + 1) bits =
          (2 * n + totalCounterSteps n (updated bits)) + (counterSteps bits + 2) := by
        rw [totalCounterSteps]
        omega
      rw [htime, Function.iterate_add_apply,
        controller_nonterminal_cycle pre out x y bits j (by omega) hw hp]
      have hr := ih (updated bits) (j + 1) (by rw [updated_length]; exact hw) (by omega) (by omega)
      simpa only [iterateCounter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

private theorem controller_terminal_cycle (pre out x y bits : List Bool) (j : ℕ)
    (hj : j < x.length) (hw : bits.length = y.length) (hz : value bits = 0) :
    machine.step^[counterSteps bits + 2] (streamFrame pre out x y bits j .emit) =
      resetFrame (streamFrame pre out x y (updated bits) (j + 1) (.done true))
        .resetLeft (updated bits).reverse y (y.length + 1) := by
  rw [show counterSteps bits + 2 = (counterSteps bits + 1) + 1 by omega,
    Function.iterate_succ_apply, controller_emit_step pre out x y bits j hj,
    Function.iterate_succ_apply', controller_stream_counter pre out x y bits (j + 1) hw,
    (underflow_iff_zero bits).mpr hz]
  exact controller_done_true_step pre out x y (updated bits) (j + 1) (by rw [updated_length]; exact hw)

/-- The last (B-th) emission detects underflow, then takes its actual dispatch
transition into reset. All previous emissions remain in the same finite loop. -/
private theorem controller_block_run (pre out x y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits]
      (streamFrame pre out x y bits j .emit) =
        resetFrame (streamFrame pre out x y last (j + (value bits + 1)) (.done true))
          .resetLeft last.reverse y (y.length + 1) := by
  dsimp only
  have hn : (iterateCounter (value bits) bits).length = y.length := by
    rw [iterate_counter_length]
    exact hw
  have hz : value (iterateCounter (value bits) bits) = 0 := by
    rw [countdown_value bits (value bits) le_rfl]
    omega
  have ht : 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits =
      (counterSteps (iterateCounter (value bits) bits) + 2) +
        (2 * value bits + totalCounterSteps (value bits) bits) := by
    rw [total_counter_steps_succ]
    omega
  rw [ht, Function.iterate_add_apply, controller_loop_run pre out x y (value bits) bits j hw le_rfl (by omega),
    controller_terminal_cycle pre out x y (iterateCounter (value bits) bits) (j + value bits) (by omega) hn hz]
  simp only [Nat.add_assoc]

/-- Complete live block, including every payload, counter, dispatch, and reset
transition. The final full configuration also records both returned work heads. -/
private theorem controller_block_reset_run (pre out x y bits : List Bool) (j : ℕ)
    (hw : bits.length = y.length) (hx : j + (value bits + 1) ≤ x.length) :
    let last := updated (iterateCounter (value bits) bits)
    machine.step^[2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2)]
      (streamFrame pre out x y bits j .emit) =
        resetFrame (streamFrame pre out x y last (j + (value bits + 1)) (.done true))
          .halt y y (y.length + 1) := by
  dsimp only
  have hl : (updated (iterateCounter (value bits) bits)).reverse.length = y.length := by
    rw [List.length_reverse, updated_length, iterate_counter_length]
    exact hw
  rw [show 2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits + (2 * y.length + 2) =
      (2 * y.length + 2) + (2 * (value bits + 1) + totalCounterSteps (value bits + 1) bits) by omega,
    Function.iterate_add_apply, controller_block_run pre out x y bits j hw hx]
  have hr := template_reset_correct
    (streamFrame pre out x y (updated (iterateCounter (value bits) bits)) (j + (value bits + 1)) (.done true))
      (updated (iterateCounter (value bits) bits)).reverse y hl
  rw [hl] at hr
  exact hr


end IntMul.CountedStream

open IntMul IntMul.CountedStream
open IntMul.TapeCopy (Sym)

theorem solution (pre out x y : List Bool) (hx : IntMul.val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(IntMul.val y+1)+4*y.length+2 ∧
      machine.step^[t] (BitDFT.CountedBlock.frame pre out x y y.reverse 0 .emit) =
        BitDFT.CountedBlock.frame pre out x y y.reverse (IntMul.val y+1) .halt := by
  have hv : value y.reverse = IntMul.val y := by
    change IntMul.BinaryAdder.littleVal y.reverse = IntMul.val y
    rw [← IntMul.BinaryAdder.val_reverse_little,List.reverse_reverse]
  let clock := 2*(value y.reverse+1)+totalCounterSteps (value y.reverse+1) y.reverse+(2*y.length+2)
  let last := updated (iterateCounter (value y.reverse) y.reverse)
  have hr := controller_block_reset_run pre out x y y.reverse 0 (by simp) (by simpa [hv] using hx)
  have hf : resetFrame (streamFrame pre out x y last (value y.reverse+1) (.done true))
      .halt y y (y.length+1) = streamFrame pre out x y y.reverse (value y.reverse+1) .halt := by
    apply controller_cfg_ext
    · rfl
    · funext i
      fin_cases i <;> simp [streamFrame,BitDFT.CountedBlock.frame,resetFrame]
    · funext i
      fin_cases i <;> simp [streamFrame,BitDFT.CountedBlock.frame,resetFrame]
  refine ⟨clock,?_,?_⟩
  · have hc := total_counter_steps_bound (value y.reverse+1) y.reverse
    dsimp only [clock]
    rw [List.length_reverse,hv] at hc
    rw [hv]
    omega
  · dsimp only at hr
    simp only [Nat.zero_add] at hr
    rw [hf] at hr
    simpa only [clock,hv] using hr
