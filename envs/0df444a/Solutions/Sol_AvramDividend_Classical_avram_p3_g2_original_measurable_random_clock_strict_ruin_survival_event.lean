-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_measurable_random_clock_strict_ruin_survival_event
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:34:51.811342+00:00
-- url     : https://prove2.me/submissions/b7c1d02d-0d7a-47d8-8666-3098b567651f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original strictly pre-ruin survival event is measurable for any
    measurable physical random clock, with the strict endpoint preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (hτMeas : Measurable τ) :
    MeasurableSet {ω : Ω |
      (τ ω : ℝ≥0∞) < ruinTime X x D ω} := by
  have hτENN : Measurable (fun ω : Ω => (τ ω : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr hτMeas
  exact measurableSet_lt hτENN (ruinTime_measurable X x D hD)
