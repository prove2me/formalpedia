-- Prove2me | solution 1 for DeciSigma1.Arithmetic.double_exp2_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:28.512219+00:00
-- url     : https://prove2.me/submissions/ea7f2916-ce4c-4a2f-a885-633985b13a20

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (a c : ℕ) : (exp2 (exp2 a)) ^ c ≤
    exp2 (exp2 (a + c)) := by
  rw [← exp2_mul, exp2_add a c]
  exact exp2_mono (Nat.mul_le_mul_left _ (le_exp2 c))
end DeciSigma1.Arithmetic
