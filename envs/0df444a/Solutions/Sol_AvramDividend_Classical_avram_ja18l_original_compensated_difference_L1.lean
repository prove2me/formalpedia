-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18l_original_compensated_difference_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:19:19.607194+00:00
-- url     : https://prove2.me/submissions/427f8e2e-2bc4-4b92-9b3a-9a4133c414ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original centred X and integrable residual have an L1 difference. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (R : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P) :
    ∀ t : ℝ≥0,
      Integrable (fun ω =>
        X.X t ω - (t : ℝ) * (∫ η, X.X 1 η ∂P) - R t ω) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  exact ((avram_ja18_standing_X_integrable_fixedtime X hX t).sub
    (integrable_const ((t : ℝ) * (∫ η, X.X 1 η ∂P)))).sub (hRint t)
