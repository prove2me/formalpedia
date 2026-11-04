-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_all_horizon_marked_finite_cells_compensate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:55:59.280209+00:00
-- url     : https://prove2.me/submissions/ac441e08-f83d-4ef2-8272-e9026c5f3953

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
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
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
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
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
      N ((Ioc s t ×ˢ A) ×ˢ B) := by
  rcases le_total s T with hsT | hTs
  · have hs' : s ≤ min t T := le_min hst hsT
    calc
      (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
          (M.restrict {p | p.1.1 ≤ T})
            ((Ioc s (min t T) ×ˢ A) ×ˢ B) := by
        rw [avram_p3_b_bvjump_original_marked_restricted_cell_measure
          𝓕 M s t T A hA B hB]
        rw [avram_p3_b_bvjump_original_marked_restricted_cell_measure
          𝓕 M s (min t T) T A hA B hB]
        rw [min_eq_left (min_le_right t T)]
      _ = N ((Ioc s (min t T) ×ˢ A) ×ˢ B) :=
        avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
          X T M hRate μ hμclock N hN s (min t T)
          hs' (min_le_right t T) A hA B hB
      _ = N ((Ioc s t ×ˢ A) ×ˢ B) :=
        (avram_p3_b_bvjump_original_Xnu_marked_intensity_horizon_clip
          X T μ hμclock N hN s t A hA B).symm
  · calc
      (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) = 0 :=
        avram_p3_b_bvjump_original_marked_cell_after_horizon_zero
          𝓕 M s t T hTs A hA B hB
      _ = N ((Ioc s t ×ˢ A) ×ˢ B) :=
        (avram_p3_b_bvjump_original_Xnu_marked_intensity_after_horizon_zero
          X T μ hμclock N hN s t hTs A hA B).symm
