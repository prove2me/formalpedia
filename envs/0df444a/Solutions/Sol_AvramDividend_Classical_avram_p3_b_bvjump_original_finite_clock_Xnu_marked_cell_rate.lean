-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:37:18.114105+00:00
-- url     : https://prove2.me/submissions/fa25e96a-46c4-4d1f-be5b-d9c16626d312

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
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
    (s t : ℝ≥0) (htT : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) :
    N ((Ioc s t ×ˢ A) ×ˢ B) =
      (ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * P A) * X.ν B := by
  calc
    N ((Ioc s t ×ˢ A) ×ˢ B) =
        μ (Ioc s t ×ˢ A) * X.ν B :=
      avram_p3_b_bvjump_original_Xnu_physical_intensity_cell
        X μ N hN s t A B
    _ = (ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * P A) * X.ν B := by
      rw [avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
        𝓕 T μ hμclock s t htT A hA]
