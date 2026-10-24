-- Prove2me | solution 1 for AvramDividend.Classical.levy_finite_grid_stopping_increment_exp_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T17:12:06.563518+00:00
-- url     : https://prove2.me/submissions/2fd19543-57fd-44fe-a8ae-1ac80d337e26

import Theorems.Thm_AvramDividend_Classical_levy_finite_grid_stopping_increment_laplace
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The stopped exponential's second moment is the stopped Laplace
identity evaluated at the doubled parameter, independently of the grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 ∂P =
      Real.exp ((h : ℝ) * X.ψ (2 * θ)) := by
  have heq :
      (fun ω => (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2) =
        (fun ω => Real.exp ((2 * θ) * (X.X (τ ω + h) ω - X.X (τ ω) ω))) := by
    funext ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact levy_finite_grid_stopping_increment_laplace
    X τ grid hgrid hstop h (2 * θ) (by positivity)
