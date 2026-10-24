-- Prove2me | solution 1 for AvramDividend.Classical.capped_random_horizon_surviving_reserve_expected_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:07:06.316393+00:00
-- url     : https://prove2.me/submissions/d3f30121-68a5-42c8-af77-482a1df5a763

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At any path-dependent horizon, surviving capped reserves have bounded expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) :
    (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      ENNReal.ofReal (riskProcess X x D (τ ω) ω) else 0 ∂P) ≤ C := by
  haveI : IsProbabilityMeasure P := X.isProbability
  calc
    (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      ENNReal.ofReal (riskProcess X x D (τ ω) ω) else 0 ∂P) ≤
        ∫⁻ _ : Ω, C ∂P := by
      apply lintegral_mono
      intro ω
      change (if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (riskProcess X x D (τ ω) ω) else 0) ≤ C
      split_ifs with hSurvive
      · exact (capped_riskProcess_range_before_ruin_including_zero
          X x hx C hxC D hD ω (τ ω) hSurvive).2
      · exact bot_le
    _ = C := by simp
