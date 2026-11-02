-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_zero_constant_polynomial_exact_finite_exp_modes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:09:43.534008+00:00
-- url     : https://prove2.me/submissions/e9f6f0a6-96be-4d70-a9a0-c024ec413c27

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open scoped BigOperators

/-! A zero-constant polynomial evaluated in exponential coordinates is exactly
a finite signed sum of strictly positive integer exponential modes. -/
theorem solution (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0)
    (r : ℝ) :
    Polynomial.eval (Real.exp (-r)) p =
      ∑ k ∈ p.support.erase 0,
        p.coeff k * Real.exp ((k : ℝ) * (-r)) := by
  calc
    Polynomial.eval (Real.exp (-r)) p =
        Polynomial.eval (Real.exp (-r)) p - Polynomial.eval 0 p := by
          rw [hp]
          ring
    _ = ∑ k ∈ p.support,
          p.coeff k * ((Real.exp (-r)) ^ k - (0 : ℝ) ^ k) := by
          rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
          change (∑ k ∈ p.support, p.coeff k * (Real.exp (-r)) ^ k) -
              (∑ k ∈ p.support, p.coeff k * (0 : ℝ) ^ k) = _
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ k ∈ p.support.erase 0,
          p.coeff k * ((Real.exp (-r)) ^ k - (0 : ℝ) ^ k) :=
        (Finset.sum_erase p.support (by simp)).symm
    _ = ∑ k ∈ p.support.erase 0,
          p.coeff k * Real.exp ((k : ℝ) * (-r)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
          simp only [zero_pow hk0, sub_zero]
          rw [Real.exp_nat_mul]
