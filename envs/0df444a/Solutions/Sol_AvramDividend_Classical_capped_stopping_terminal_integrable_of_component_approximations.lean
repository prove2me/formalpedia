-- Prove2me | solution 1 for AvramDividend.Classical.capped_stopping_terminal_integrable_of_component_approximations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:36:57.897345+00:00
-- url     : https://prove2.me/submissions/93fc6562-66aa-4c57-9d21-79cf92b187ef

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_of_progressive_components

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Progressive pointwise approximations yield stopped HJB terminal integrability under a finite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)))
    (UX UD : ℕ → ℝ≥0 → Ω → ℝ)
    (hUX : ∀ n, ProgMeasurable 𝓕 (UX n))
    (hUD : ∀ n, ProgMeasurable 𝓕 (UD n))
    (hXtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UX n t ω) Filter.atTop (nhds (X.X t ω)))
    (hDtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UD n t ω) Filter.atTop (nhds (D t ω))) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by
  have hXProg : ProgMeasurable 𝓕 X.X :=
    progressive_of_pointwise_progressive_approximants UX X.X hUX hXtendsto
  have hDProg : ProgMeasurable 𝓕 D :=
    progressive_of_pointwise_progressive_approximants UD D hUD hDtendsto
  exact capped_stopping_terminal_integrable_of_progressive_components
    X w hw B hB x hx hxc D hD τ hStop hXProg hDProg
