-- Prove2me | solution 1 for DeciSigma1.Arithmetic.two_mul_iterate_exp2_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:35.245047+00:00
-- url     : https://prove2.me/submissions/0409d9f7-79c4-4eff-b8db-419cd328352a

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_strictMono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution (h x : ℕ) (hh : 1 ≤ h) :
    2 * exp2^[h] x ≤ exp2^[h] (x + 1) := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  have hi := (exp2_strictMono.iterate h) (Nat.lt_succ_self x)
  calc
    2 * exp2 (exp2^[h] x) = exp2 (exp2^[h] x + 1) := by
      rw [exp2_add]; simp [exp2, Nat.mul_comm]
    _ ≤ exp2 (exp2^[h] (x + 1)) := exp2_mono hi
end DeciSigma1.Arithmetic
