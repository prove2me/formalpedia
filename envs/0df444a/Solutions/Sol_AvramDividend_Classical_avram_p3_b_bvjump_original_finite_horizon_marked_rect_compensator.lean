-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:41:38.636034+00:00
-- url     : https://prove2.me/submissions/a30a98dc-a789-4506-aa62-3ae00ca39f1f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_horizon_restricted_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
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
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
      N ((Ioc s t ×ˢ A) ×ˢ B) := by
  have hsT : s ≤ T := hst.trans htT
  calc
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
      simpa [min_eq_left htT] using
        (avram_p3_b_bvjump_original_horizon_restricted_source_rate
          X M hRate s t T hst hsT A hA B hB)
    _ = (ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * P A) * X.ν B := by
      rw [avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
        s t hst]
      ac_rfl
    _ = N ((Ioc s t ×ˢ A) ×ˢ B) :=
      (avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
        X T μ hμclock N hN s t htT A hA B).symm
