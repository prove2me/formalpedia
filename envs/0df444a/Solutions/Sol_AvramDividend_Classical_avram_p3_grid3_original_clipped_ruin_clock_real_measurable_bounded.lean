-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_clipped_ruin_clock_real_measurable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:32:48.696538+00:00
-- url     : https://prove2.me/submissions/1c78d131-5841-4f4d-a014-c666bf14cf9a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual ruin-clipped physical horizon is a bounded measurable real clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal) ∧
    (∀ ω : Ω,
      0 ≤ (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal ∧
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toReal ≤ (T : ℝ)) := by
  have hτ : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD
  constructor
  · exact (hτ.min measurable_const).ennreal_toReal
  · intro ω
    constructor
    · exact ENNReal.toReal_nonneg
    · have hm :
        min (ruinTime X x D ω) (T : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
        min_le_right _ _
      have hr := ENNReal.toReal_mono ENNReal.coe_ne_top hm
      simpa using hr
