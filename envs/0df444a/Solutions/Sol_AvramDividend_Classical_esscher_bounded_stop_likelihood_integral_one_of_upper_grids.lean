-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one_of_upper_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T18:31:19.94944+00:00
-- url     : https://prove2.me/submissions/9a983ed9-bbdf-4d2c-8630-c1c6c8819780

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by
  have hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P :=
    esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
      X θ hθ T H τn grid hgrid hT hstop hbound
  exact esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids
    X θ hθ T τ τn grid hgrid hT hstop hlim habove hUI
