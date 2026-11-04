-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_horizon_restricted_source_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:58:17.192218+00:00
-- url     : https://prove2.me/submissions/0c2f3ced-d8c7-43fe-9b11-0921ce23eaf6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_marked_restricted_cell_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (s t T : ℝ≥0) (hst : s ≤ t) (hsT : s ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
    P A * (((min t T - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by
  rw [avram_p3_b_bvjump_original_marked_restricted_cell_measure
    𝓕 M s t T A hA B hB]
  exact hRate s (min t T) (le_min hst hsT) A hA B hB
