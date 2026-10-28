-- Prove2me | solution 1 for AvramDividend.Classical.localized_stopped_terminal_expected_le_of_uniform_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:54:30.594425+00:00
-- url     : https://prove2.me/submissions/2c56b107-1654-47b9-ad25-2da4dad04f60

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_localized_stopped_terminal_lintegral_iSup_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform expected terminal bounds on all finite reserve bands control the entire stopped HJB terminal payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D))
    (K : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
        0 ≤ stoppedValue (riskProcess X x D) τ ω ∧
        stoppedValue (riskProcess X x D) τ ω ≤ (n : ℝ) then
          ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
        else 0 ∂P) ≤ K) :
    (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
      0 ≤ stoppedValue (riskProcess X x D) τ ω then
        ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
      else 0 ∂P) ≤ K := by
  rw [localized_stopped_terminal_lintegral_iSup_bands
    X w hw hw_neg x D hD τ hτ hProg]
  exact iSup_le hBound
