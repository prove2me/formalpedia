-- Prove2me | solution 1 for AvramDividend.Classical.localized_stopping_terminal_integrable_of_component_approximations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:42:55.985782+00:00
-- url     : https://prove2.me/submissions/1d937b2e-40af-417d-8e8c-873e28d5a1a8

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_progressive_of_pointwise_component_approximations
import Theorems.Thm_AvramDividend_Classical_localized_stopping_terminal_integrable_from_progressive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The stopped terminal HJB payoff is integrable on every finite reserve band when the reserve has progressive component approximations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (UX UD : ℕ → ℝ≥0 → Ω → ℝ)
    (hUX : ∀ n, ProgMeasurable 𝓕 (UX n))
    (hUD : ∀ n, ProgMeasurable 𝓕 (UD n))
    (hXtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UX n t ω) Filter.atTop (nhds (X.X t ω)))
    (hDtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UD n t ω) Filter.atTop (nhds (D t ω))) :
    Integrable (fun ω =>
      if τ ω < ruinTime X x D ω then
        if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0
      else 0) P := by
  have hProg : ProgMeasurable 𝓕 (riskProcess X x D) :=
    riskProcess_progressive_of_pointwise_component_approximations
      X x D UX UD hUX hUD hXtendsto hDtendsto
  exact localized_stopping_terminal_integrable_from_progressive
    X w hw B hB x D hD τ hτ hProg
