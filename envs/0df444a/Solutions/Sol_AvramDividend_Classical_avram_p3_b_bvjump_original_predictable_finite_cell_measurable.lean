-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_finite_cell_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.45946+00:00
-- url     : https://prove2.me/submissions/5d514899-58f0-4ed3-a643-ffc76dc2ffc0

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
    (s t : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      ((Ioc s t ×ˢ A) ×ˢ B) := by
  have hAplus : MeasurableSet[𝓕.rightCont s] A :=
    (𝓕.le_rightCont s A) hA
  have hp : MeasurableSet[𝓕.rightCont.predictable]
      (Ioc s t ×ˢ A) :=
    measurableSet_predictable_Ioc_prod s t hAplus
  exact hp.prod hB
