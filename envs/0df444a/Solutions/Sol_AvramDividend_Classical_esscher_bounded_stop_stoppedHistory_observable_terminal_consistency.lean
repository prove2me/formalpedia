-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_terminal_consistency
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:14:12.951073+00:00
-- url     : https://prove2.me/submissions/143db0ab-ae2f-4125-88a8-e6d0d91a1cd0

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T₁ T₂ : ℝ≥0) (hT₁ : H + 1 ≤ T₁)
    (hT₂ : H + 1 ≤ T₂)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYstopped : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))) =
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))) := by
  rw [AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_map_law X θ hθ τ hstop H hbound
      T₁ hT₁ Y hY hYstopped,
    AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_observable_map_law X θ hθ τ hstop H hbound
      T₂ hT₂ Y hY hYstopped]