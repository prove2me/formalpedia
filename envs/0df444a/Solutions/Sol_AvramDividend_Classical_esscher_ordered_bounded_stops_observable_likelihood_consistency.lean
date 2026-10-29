-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_observable_likelihood_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:56:03.292066+00:00
-- url     : https://prove2.me/submissions/c034cb38-7574-47a3-9cc6-ac6d9e4e29d8

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_likelihood_history_consistency
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    {β : Type*} [MeasurableSpace β] (Y : Ω → β)
    (hY : Measurable Y)
    (hYτ : ∀ (B : Set β), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((Y ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω -
          (τ ω : ℝ) * X.ψ θ)))) =
    Measure.map Y
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (θ * X.X (σ ω) ω -
          (σ ω : ℝ) * X.ψ θ)))) := by
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply hY hB, Measure.map_apply hY hB]
  exact esscher_ordered_bounded_stops_likelihood_history_consistency
    X θ hθ τ σ hstopτ hstopσ horder H hboundσ T hT
    (Y ⁻¹' B) (hYτ B hB)
