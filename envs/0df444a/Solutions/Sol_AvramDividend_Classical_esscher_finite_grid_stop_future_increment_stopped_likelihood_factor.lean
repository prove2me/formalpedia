-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_future_increment_stopped_likelihood_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:32:01.189221+00:00
-- url     : https://prove2.me/submissions/73a0d491-d2a5-4d1e-9a06-ed3f819a66b6

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
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
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  have hTstop : ∀ s ∈ grid, s ≤ T := by
    intro s hs
    exact le_trans le_self_add (hT s hs)
  calc
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
        ((X.X u) ⁻¹' B) :=
      esscher_finite_grid_stop_future_increment_cylinder_factor
        X θ hθ T u τ grid hgrid hT hstop A hA hHistory B hB
    _ = (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) A *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
        ((X.X u) ⁻¹' B) := by
      rw [esscher_finite_grid_stop_likelihood_history
        X θ hθ T τ grid hgrid hTstop hstop A hA hHistory]
