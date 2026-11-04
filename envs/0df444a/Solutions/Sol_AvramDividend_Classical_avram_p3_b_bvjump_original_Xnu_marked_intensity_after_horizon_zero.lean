-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:43:30.50626+00:00
-- url     : https://prove2.me/submissions/e2d1af6f-5c58-49c9-ab97-3fee0ec5f084

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_after_horizon_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (s t : ℝ≥0) (hTs : T ≤ s)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) = 0 := by
  have hAplus : MeasurableSet[𝓕.rightCont s] A :=
    (𝓕.le_rightCont s A) hA
  have hE : MeasurableSet[𝓕.rightCont.predictable]
      (Ioc s t ×ˢ A) :=
    measurableSet_predictable_Ioc_prod s t hAplus
  have hμzero : μ (Ioc s t ×ˢ A) = 0 := by
    rw [hμclock (Ioc s t ×ˢ A) hE]
    rw [Measure.prod_prod]
    rw [avram_p3_b_bvjump_original_clock_after_horizon_zero
      s t T hTs]
    simp
  calc
    N ((Ioc s t ×ˢ A) ×ˢ B) =
        μ (Ioc s t ×ˢ A) * X.ν B :=
      avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
        X μ N hN s t A B
    _ = 0 := by rw [hμzero]; simp
