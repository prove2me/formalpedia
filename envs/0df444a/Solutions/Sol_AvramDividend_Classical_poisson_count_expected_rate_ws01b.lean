-- Prove2me | solution 1 for AvramDividend.Classical.poisson_count_expected_rate_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:29:34.517533+00:00
-- url     : https://prove2.me/submissions/75f19fa3-74a1-4829-8876-569968be773f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal Nat

/-- The Poisson jump count has mean equal to its rate, in Bochner integral form.
This is the scalar Campbell starting point for BV Lévy compensators. -/
theorem solution (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂(poissonMeasure r)) = (r : ℝ) := by
  have hmass :
      HasSum (fun n : ℕ => (poissonMeasure r).real {n}) 1 := by
    simpa only [poissonMeasure_real_singleton] using
      hasSum_one_poissonMeasure r
  have hshift (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) * (poissonMeasure r).real {n + 1} =
        (r : ℝ) * (poissonMeasure r).real {n} := by
    simp only [poissonMeasure_real_singleton, Nat.factorial_succ,
      Nat.cast_mul, pow_succ]
    have hf : ((n ! : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  have hExp :
      HasSum (fun n : ℕ =>
        (n : ℝ) * (poissonMeasure r).real {n}) (r : ℝ) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    simp_rw [hshift]
    simpa [mul_one] using hmass.mul_left (r : ℝ)
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  refine (tsum_congr fun n => ?_).trans hExp.tsum_eq
  rw [poissonMeasure_real_singleton]
  ring
