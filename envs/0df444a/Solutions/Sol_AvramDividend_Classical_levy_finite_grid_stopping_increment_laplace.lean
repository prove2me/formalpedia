-- Prove2me | solution 1 for AvramDividend.Classical.levy_finite_grid_stopping_increment_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:32:04.990455+00:00
-- url     : https://prove2.me/submissions/caa7a06a-0505-41f0-8595-f827d2f71b60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finite_grid_partition_expectation
import Theorems.Thm_AvramDividend_Classical_levy_future_increment_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_increment_laplace_on_past_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
      Real.exp ((h : ℝ) * X.ψ θ) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : ℝ≥0 → Ω → ℝ :=
    fun s ω => Real.exp (θ * (X.X (s + h) ω - X.X s ω))
  have hm : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s} := by
    intro s hs
    exact (𝓕.le s) _ (hstop s hs)
  have hi : ∀ s ∈ grid, Integrable (f s) P := by
    intro s hs
    exact AvramDividend.Classical.levy_future_increment_exp_integrable
      X s h θ hθ
  have heach : ∀ s ∈ grid,
      ∫ ω in {ω : Ω | τ ω = s}, f s ω ∂P =
        (P {ω : Ω | τ ω = s}).toReal *
          Real.exp ((h : ℝ) * X.ψ θ) := by
    intro s hs
    exact AvramDividend.Classical.levy_increment_laplace_on_past_event
      X s h {ω : Ω | τ ω = s} (hstop s hs) θ hθ
  exact AvramDividend.Classical.finite_grid_partition_expectation
    τ grid hgrid hm f hi (Real.exp ((h : ℝ) * X.ψ θ)) heach
