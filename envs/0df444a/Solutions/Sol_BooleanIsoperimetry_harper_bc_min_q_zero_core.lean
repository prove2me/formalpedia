-- Prove2me | solution 1 for BooleanIsoperimetry.harper_bc_min_q_zero_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:15.315083+00:00
-- url     : https://prove2.me/submissions/5bd35428-719c-498e-8100-05a17e164235

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) {a b p : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit n (a + b) p 0) :
    H n p + p ≤ max (H n a) b + max (H n b) a := by
  rcases hcasc with ⟨ r, t, hr, rfl, ht ⟩;
  rcases r with ( _ | r ) <;>
    simp +arith +decide only [cascadeSlice1Value, zero_tsub, add_tsub_cancel_right] at ht ⊢;
  · cases hr; norm_num [ binomPrefix, choosePred ] at *;
    aesop;
  · rcases r with ( _ | r ) <;>
    simp +arith +decide only [binomPrefix_succ, choosePred, zero_add] at ht ⊢;
    · rcases t with ( _ | _ | t ) <;>
      simp +arith +decide only [binomPrefix_zero, ↓reduceIte, tsub_self,
        Nat.choose_zero_right, zero_le, inf_of_le_left, add_zero, zero_add,
        zero_ne_one, le_add_iff_nonneg_left, inf_of_le_right] at ht ⊢;
      simp +arith +decide only [cascadeSlice0Value, binomPrefix, zero_add,
        Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, zero_tsub,
        add_zero, Order.add_one_le_iff] at hpq ⊢;
      rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp +arith +decide at *;
    · rw [ eq_comm ] at ht; simp_all +arith +decide [ binomPrefix ];
      grind +suggestions
end BooleanIsoperimetry
