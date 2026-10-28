-- Prove2me | solution 1 for AvramDividend.Classical.normalized_laplace_tilt_is_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:36:10.979755+00:00
-- url     : https://prove2.me/submissions/a7a43579-7dc5-403d-8d8a-cab75012c633

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (s₀ C : ℝ)
    (hC : C = ∫ x, Real.exp (-(s₀ * x)) ∂μ)
    (hCpos : 0 < C)
    (hInt : Integrable (fun x : ℝ => Real.exp (-(s₀ * x))) μ) :
    IsProbabilityMeasure
      (μ.withDensity (fun x => ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x))))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hInt.const_mul C⁻¹)
      (Filter.Eventually.of_forall fun x => by positivity),
    integral_const_mul, ← hC, inv_mul_cancel₀ hCpos.ne', ENNReal.ofReal_one]
