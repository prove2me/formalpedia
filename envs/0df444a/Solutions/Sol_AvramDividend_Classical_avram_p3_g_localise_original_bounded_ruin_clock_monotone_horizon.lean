-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_bounded_ruin_clock_monotone_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:23:05.062199+00:00
-- url     : https://prove2.me/submissions/ca6ac404-5ef7-4bbb-bf17-0e40129aff06

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual finite original ruin-truncated clocks are pathwise monotone
as the deterministic horizon increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T₁ T₂ : ℝ≥0) (hT : T₁ ≤ T₂) :
    ∀ ω : Ω,
      (min (ruinTime X x D ω) (T₁ : ℝ≥0∞)).toNNReal ≤
      (min (ruinTime X x D ω) (T₂ : ℝ≥0∞)).toNNReal := by
  intro ω
  have hF₁ :
      min (ruinTime X x D ω) (T₁ : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt
      ((min_le_right (ruinTime X x D ω) (T₁ : ℝ≥0∞)).trans_lt
        ENNReal.coe_lt_top)
  have hF₂ :
      min (ruinTime X x D ω) (T₂ : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt
      ((min_le_right (ruinTime X x D ω) (T₂ : ℝ≥0∞)).trans_lt
        ENNReal.coe_lt_top)
  have hMin :
      min (ruinTime X x D ω) (T₁ : ℝ≥0∞) ≤
      min (ruinTime X x D ω) (T₂ : ℝ≥0∞) := by
    exact min_le_min_left (ruinTime X x D ω)
      (ENNReal.coe_le_coe.mpr hT)
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_toNNReal hF₁, ENNReal.coe_toNNReal hF₂]
  exact hMin
