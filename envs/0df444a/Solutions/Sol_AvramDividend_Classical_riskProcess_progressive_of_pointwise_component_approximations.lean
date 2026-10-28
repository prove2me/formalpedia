-- Prove2me | solution 1 for AvramDividend.Classical.riskProcess_progressive_of_pointwise_component_approximations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:23:37.374318+00:00
-- url     : https://prove2.me/submissions/cbb4f40d-aeac-4241-bca8-b0f493873527

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants
import Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_progressive_parts

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Pointwise progressive approximations of Lévy noise and dividends give a progressive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (UX UD : ℕ → ℝ≥0 → Ω → ℝ)
    (hUX : ∀ n, ProgMeasurable 𝓕 (UX n))
    (hUD : ∀ n, ProgMeasurable 𝓕 (UD n))
    (hXtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UX n t ω) Filter.atTop (nhds (X.X t ω)))
    (hDtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UD n t ω) Filter.atTop (nhds (D t ω))) :
    ProgMeasurable 𝓕 (riskProcess X x D) := by
  have hXProg : ProgMeasurable 𝓕 X.X :=
    progressive_of_pointwise_progressive_approximants UX X.X hUX hXtendsto
  have hDProg : ProgMeasurable 𝓕 D :=
    progressive_of_pointwise_progressive_approximants UD D hUD hDtendsto
  exact riskProcess_progMeasurable_of_progressive_parts X x D hXProg hDProg
