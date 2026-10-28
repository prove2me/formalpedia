-- Prove2me | solution 1 for AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:34:22.971705+00:00
-- url     : https://prove2.me/submissions/b7bc49ec-91a5-4230-947b-0704c685979f

import Mathlib
open MeasureTheory Set
open scoped ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (hunit : ∀ t : ℝ, (∫⁻ ω, D (ω, t) ∂P) = 1) :
    IsProbabilityMeasure ((P.prod η).withDensity D) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_prod_symm _ hD.aemeasurable]
  simp [hunit]
