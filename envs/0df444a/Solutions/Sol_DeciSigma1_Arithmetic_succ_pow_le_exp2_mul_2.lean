-- Prove2me | solution 2 for DeciSigma1.Arithmetic.succ_pow_le_exp2_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:53.88406+00:00
-- url     : https://prove2.me/submissions/bbc61789-ecea-432d-8e49-9e66610dc609

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_succ_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (x d : ℕ) : (x + 1) ^ d ≤ exp2 (d * x) := by
  calc
    _ ≤ exp2 x ^ d := Nat.pow_le_pow_left (succ_le_exp2 x) d
    _ = exp2 (d * x) := by rw [← exp2_mul, Nat.mul_comm]
end DeciSigma1.Arithmetic
