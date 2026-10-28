-- Prove2me | solution 2 for AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:34:31.257216+00:00
-- url     : https://prove2.me/submissions/cfe9d5b3-9921-46dc-8f04-d0f414ffeacd

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (hunit : ∀ t : ℝ, (∫⁻ ω, D (ω, t) ∂P) = 1) :
    IsProbabilityMeasure ((P.prod η).withDensity D) := by
  rw [isProbabilityMeasure_iff]
  calc
    ((P.prod η).withDensity D) Set.univ =
        (∫⁻ z, D z ∂(P.prod η)) := by
          rw [withDensity_apply D MeasurableSet.univ]
          simp
    _ = (∫⁻ t : ℝ, ∫⁻ ω, D (ω, t) ∂P ∂η) :=
      lintegral_prod_symm D hD.aemeasurable
    _ = 1 := by
      simp only [hunit]
      simp
