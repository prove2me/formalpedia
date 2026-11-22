-- Prove2me | solution 1 for DeciSigma1.Arithmetic.iterate_exp2_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:25.428222+00:00
-- url     : https://prove2.me/submissions/d72594ab-a2ea-41b7-8fd3-5f85418e86f7

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_add_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (h a b : ℕ) (hh : 1 ≤ h) :
    exp2^[h] a * exp2^[h] b ≤ exp2^[h] (a + b + 1) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_succ_apply', ← exp2_add]
  apply exp2_mono
  cases h with
  | zero => simp
  | succ h => exact iterate_exp2_add_le _ _ _ (by omega)
end DeciSigma1.Arithmetic
