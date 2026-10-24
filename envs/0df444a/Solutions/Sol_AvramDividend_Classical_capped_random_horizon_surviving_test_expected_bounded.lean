-- Prove2me | solution 1 for AvramDividend.Classical.capped_random_horizon_surviving_test_expected_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:57:33.21033+00:00
-- url     : https://prove2.me/submissions/baca96c7-0077-4274-aca6-32d64c020878

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A finite cap bounds the expected absolute HJB terminal value at random horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) ≤
      ENNReal.ofReal M := by
  haveI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB hw
  refine ⟨M, hM0, ?_⟩
  calc
    (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|w (riskProcess X x D (τ ω) ω)|) else 0 ∂P) ≤
        ∫⁻ _ : Ω, ENNReal.ofReal M ∂P := by
      apply lintegral_mono
      intro ω
      change (if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        ENNReal.ofReal (|w (riskProcess X x D (τ ω) ω)|) else 0) ≤
        ENNReal.ofReal M
      split_ifs with hSurvive
      · obtain ⟨hNonneg, hCap⟩ :=
          capped_riskProcess_range_before_ruin_including_zero
            X x hx (ENNReal.ofReal B) hxc D hD ω (τ ω) hSurvive
        have hUpper : riskProcess X x D (τ ω) ω ≤ B :=
          (ENNReal.ofReal_le_ofReal_iff hB).mp hCap
        exact ENNReal.ofReal_le_ofReal (hM _ hNonneg hUpper)
      · exact bot_le
    _ = ENNReal.ofReal M := by simp
