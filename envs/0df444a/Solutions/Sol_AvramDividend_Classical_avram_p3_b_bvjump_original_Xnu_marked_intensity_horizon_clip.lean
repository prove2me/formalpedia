-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:51:37.01773+00:00
-- url     : https://prove2.me/submissions/ac06e989-b889-42f2-a9a4-bd93882d0847

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_interval_mass_clipped
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
    (s t : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      N ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
  have hAplus : MeasurableSet[𝓕.rightCont s] A :=
    (𝓕.le_rightCont s A) hA
  have hE : MeasurableSet[𝓕.rightCont.predictable]
      (Ioc s t ×ˢ A) :=
    measurableSet_predictable_Ioc_prod s t hAplus
  have hE' : MeasurableSet[𝓕.rightCont.predictable]
      (Ioc s (min t T) ×ˢ A) :=
    measurableSet_predictable_Ioc_prod s (min t T) hAplus
  calc
    N ((Ioc s t ×ˢ A) ×ˢ B) =
        μ (Ioc s t ×ˢ A) * X.ν B :=
      avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
        X μ N hN s t A B
    _ = (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal) (Ioc s t) * P A) * X.ν B) := by
      rw [hμclock (Ioc s t ×ˢ A) hE, Measure.prod_prod]
    _ = (((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal) (Ioc s (min t T)) * P A) * X.ν B) := by
      rw [avram_p3_b_bvjump_original_clock_interval_mass_clipped s t T]
    _ = μ (Ioc s (min t T) ×ˢ A) * X.ν B := by
      rw [hμclock (Ioc s (min t T) ×ˢ A) hE', Measure.prod_prod]
    _ = N ((Ioc s (min t T) ×ˢ A) ×ˢ B) :=
      (avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
        X μ N hN s (min t T) A B).symm
