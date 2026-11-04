-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:37.517028+00:00
-- url     : https://prove2.me/submissions/051adf2a-4cec-468c-948d-2a85e85b62e1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (s t : ℝ≥0) (htT : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    μ (Ioc s t ×ˢ A) =
      ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * P A := by
  have hAplus : MeasurableSet[𝓕.rightCont s] A :=
    (𝓕.le_rightCont s A) hA
  have hE : MeasurableSet[𝓕.rightCont.predictable]
      (Ioc s t ×ˢ A) :=
    measurableSet_predictable_Ioc_prod s t hAplus
  rw [hμclock (Ioc s t ×ˢ A) hE]
  rw [Measure.prod_prod]
  rw [avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
    s t T htT]
