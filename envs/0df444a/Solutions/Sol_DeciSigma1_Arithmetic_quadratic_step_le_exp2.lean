-- Prove2me | solution 1 for DeciSigma1.Arithmetic.quadratic_step_le_exp2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:39.40563+00:00
-- url     : https://prove2.me/submissions/4a86f70d-dbf1-418d-b99b-b9765cc46b4e

module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Monotone.Defs
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_mono
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
namespace DeciSigma1.Arithmetic
theorem _root_.solution {t a e q L : ℕ}
    (ht : t ≤ exp2 L) (ha : a ≤ exp2 q) (he : e ≤ exp2 q) :
    t + (t * a) * ((t * a + 2) * e) ≤ exp2 (2 * L + 3 * q + 3) := by
  have hta : t * a ≤ exp2 (L + q) := by
    rw [exp2_add]; exact Nat.mul_le_mul ht ha
  have hplus : t * a + 2 ≤ exp2 (L + q + 2) :=
    (Nat.add_le_add hta (le_refl 2)).trans (exp2_add_le (L + q) 1)
  calc
    _ ≤ exp2 L + exp2 (L + q) * (exp2 (L + q + 2) * exp2 q) :=
      Nat.add_le_add ht (Nat.mul_le_mul hta (Nat.mul_le_mul hplus he))
    _ = exp2 L + exp2 (2 * L + 3 * q + 2) := by
      rw [← exp2_add, ← exp2_add]; congr 2; omega
    _ ≤ exp2 (2 * L + 3 * q + 2) + exp2 (2 * L + 3 * q + 2) :=
      Nat.add_le_add_right (exp2_mono (by omega)) _
    _ = _ := by
      rw [show 2 * L + 3 * q + 3 = (2 * L + 3 * q + 2) + 1 by omega,
        exp2_add (2 * L + 3 * q + 2) 1]
      change exp2 (2 * L + 3 * q + 2) + exp2 (2 * L + 3 * q + 2) =
        exp2 (2 * L + 3 * q + 2) * 2
      omega
end DeciSigma1.Arithmetic
