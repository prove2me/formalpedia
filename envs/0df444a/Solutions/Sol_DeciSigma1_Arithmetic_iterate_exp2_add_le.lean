-- Prove2me | solution 1 for DeciSigma1.Arithmetic.iterate_exp2_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:59.840802+00:00
-- url     : https://prove2.me/submissions/7cbc115e-24e8-4736-ad4e-3e312b2de626

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_iterate_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_two_mul_iterate_exp2_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (h a b : ℕ) (hh : 1 ≤ h) :
    exp2^[h] a + exp2^[h] b ≤ exp2^[h] (a + b + 1) := by
  calc
    _ ≤ 2 * exp2^[h] (a + b) := by
      have ha := iterate_exp2_mono h (Nat.le_add_right a b)
      have hb := iterate_exp2_mono h (Nat.le_add_left b a)
      omega
    _ ≤ _ := two_mul_iterate_exp2_le h (a + b) hh
end DeciSigma1.Arithmetic
