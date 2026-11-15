-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:44:02.632184+00:00
-- url     : https://prove2.me/submissions/acecbd5d-692c-4561-9d97-cdf36de3643c

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

theorem solution
    (θ K B y r : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hy : y ≤ B) :
    K * Real.exp (θ * (y + r)) ≤
      (K * Real.exp (θ * B)) * Real.exp (θ * r) := by
  have he : Real.exp (θ * y) ≤ Real.exp (θ * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hθ)
  calc
    K * Real.exp (θ * (y + r)) =
        (K * Real.exp (θ * y)) * Real.exp (θ * r) := by
          rw [mul_add, Real.exp_add]
          ring
    _ ≤ (K * Real.exp (θ * B)) * Real.exp (θ * r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he hK)
        (le_of_lt (Real.exp_pos _))
