-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_marked_intensity_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:28:34.281079+00:00
-- url     : https://prove2.me/submissions/8782a4eb-6283-458f-8360-2adb57e617a0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (ν : Measure ℝ) [SFinite ν]
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; μ.prod ν))
    (s t : ℝ≥0) (A : Set Ω) (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      μ (Ioc s t ×ˢ A) * ν B := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    @Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)
  rw [hN]
  exact Measure.prod_prod (Ioc s t ×ˢ A) B
