-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_independent_clock_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:57:44.245952+00:00
-- url     : https://prove2.me/submissions/52936867-f2d6-4741-8b1b-914d93fc3b0e

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (p : ℝ) (hp : 0 < p) (C : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
        (expMeasure p))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)) * (expMeasure p) C := by
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  rw [Measure.prod_prod]
  rw [esscher_finite_grid_stop_future_increment_cylinder_factor
    X θ hθ T u τ grid hgrid hT hstop A hA hHistory B hB]
