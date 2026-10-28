-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_exp_survival_drift_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:47:14.061241+00:00
-- url     : https://prove2.me/submissions/248ef4f1-a07f-45e5-a9d9-543683fc9dda

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open MeasureTheory Set
theorem solution
    (d q jumpRate : ℝ) (hq : 0 < q) (hjumpRate : 0 ≤ jumpRate) :
    (∫ t : ℝ in Ioi (0 : ℝ),
      d * Real.exp (-(q + jumpRate) * t) ∂volume) = d / (q + jumpRate) := by 
  have hp : 0 < q + jumpRate := by linarith
  have h := integral_exp_mul_Ioi (a := -(q + jumpRate)) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, zero_sub] at h
  rw [integral_const_mul, h]; field_simp
