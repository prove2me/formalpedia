-- Prove2me | solution 2 for AvramDividend.Classical.esscher_bounded_stop_future_increment_terminal_consistency_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:46:52.014975+00:00
-- url     : https://prove2.me/submissions/86f6332c-c846-4aeb-8699-5bee4d6771d4

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_map_law

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T₁ T₂ : ℝ≥0) (hT₁ : H + 1 + u ≤ T₁)
    (hT₂ : H + 1 + u ≤ T₂)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT₁ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₁ ω - (T₁ : ℝ) * X.ψ θ)))
    let QT₂ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T₂ ω - (T₂ : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT₁.restrict A) =
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT₂.restrict A) := by
  intro QT₁ QT₂
  have h1 := esscher_bounded_stop_future_increment_stopped_likelihood_map_law X θ hθ τ hstop H hbound
    u T₁ hT₁ A hA
  have h2 := esscher_bounded_stop_future_increment_stopped_likelihood_map_law X θ hθ τ hstop H hbound
    u T₂ hT₂ A hA
  exact h1.trans h2.symm
