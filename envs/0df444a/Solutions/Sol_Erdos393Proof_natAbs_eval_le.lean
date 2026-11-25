-- Prove2me | solution 1 for Erdos393Proof.natAbs_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:32:03.040939+00:00
-- url     : https://prove2.me/submissions/13cd1d77-2c69-42c5-b6f5-21b729e77cfe

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (R : ℤ[X]) {y : ℕ} (hy : 1 ≤ y) :
    (R.eval (y : ℤ)).natAbs ≤
      (∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).natAbs) * y ^ R.natDegree := by
  have hy' : (1 : ℤ) ≤ y := by exact_mod_cast hy
  have h : |R.eval (y : ℤ)| ≤
      (∑ i ∈ Finset.range (R.natDegree + 1), |R.coeff i|) * (y : ℤ) ^ R.natDegree := by
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ y)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hy' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))) (abs_nonneg _)
  zify
  simpa using h
end Erdos393Proof
