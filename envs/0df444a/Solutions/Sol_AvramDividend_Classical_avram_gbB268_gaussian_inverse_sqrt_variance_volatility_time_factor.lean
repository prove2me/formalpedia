-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB268_gaussian_inverse_sqrt_variance_volatility_time_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:35.086965+00:00
-- url     : https://prove2.me/submissions/13250e6d-6ff5-43c9-91ab-1aaebe0010a3

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- The Gaussian kernel separates source volatility and elapsed-time square root. -/
theorem solution
    (sigma dt : ℝ) (hsigma : 0 < sigma) (hdt : 0 ≤ dt) :
    (Real.sqrt (2 * Real.pi * (sigma ^ 2 * dt)))⁻¹ =
      (Real.sqrt (2 * Real.pi))⁻¹ * sigma⁻¹ * (Real.sqrt dt)⁻¹ := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hsquare : (0 : ℝ) ≤ sigma ^ 2 := sq_nonneg sigma
  calc
    (Real.sqrt (2 * Real.pi * (sigma ^ 2 * dt)))⁻¹ =
      (Real.sqrt ((2 * Real.pi * sigma ^ 2) * dt))⁻¹ := by
        congr 1
        ring
    _ = (Real.sqrt (2 * Real.pi * sigma ^ 2) * Real.sqrt dt)⁻¹ := by
      rw [Real.sqrt_mul (mul_nonneg hpi hsquare)]
    _ = ((Real.sqrt (2 * Real.pi) * Real.sqrt (sigma ^ 2)) * Real.sqrt dt)⁻¹ := by
      rw [Real.sqrt_mul hpi]
    _ = ((Real.sqrt (2 * Real.pi) * sigma) * Real.sqrt dt)⁻¹ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hsigma]
    _ = _ := by
      simp only [mul_inv_rev]
      ring
