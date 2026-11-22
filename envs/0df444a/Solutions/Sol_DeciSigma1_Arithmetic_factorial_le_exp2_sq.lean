-- Prove2me | solution 1 for DeciSigma1.Arithmetic.factorial_le_exp2_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:45.2308+00:00
-- url     : https://prove2.me/submissions/531803af-0be5-477e-9972-219b793022e3

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_le_exp2
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mul

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (n : ℕ) : n.factorial ≤ exp2 (n * n) := by
  calc
    _ ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ exp2 n ^ n := Nat.pow_le_pow_left (le_exp2 n) n
    _ = _ := (exp2_mul n n).symm
end DeciSigma1.Arithmetic
