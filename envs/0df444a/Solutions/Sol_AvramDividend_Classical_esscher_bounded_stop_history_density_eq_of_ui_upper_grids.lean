-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_history_density_eq_of_ui_upper_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:57:02.164607+00:00
-- url     : https://prove2.me/submissions/a1e996c7-0fa6-4195-b810-9101fe951d31

import Mathlib
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τn n ω = s}))
    (hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by
  let f : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)
  let g : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)
  let QT : Measure Ω := P.withDensity (fun ω =>
    ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  have hlimf : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) :=
    Eventually.of_forall
      (esscher_stopped_likelihood_tendsto_of_right_approximation
        X θ hθ τ τn hlim habove)
  have hconv : Tendsto
      (fun n => (P.withDensity (fun ω => ENNReal.ofReal (f n ω))) A)
      atTop (𝓝 ((P.withDensity (fun ω => ENNReal.ofReal (g ω))) A)) :=
    uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
      P f g hUI hlimf
      (fun n ω => (Real.exp_pos _).le)
      (fun ω => (Real.exp_pos _).le) A hA
  have hEach (n : ℕ) :
      QT A = (P.withDensity (fun ω => ENNReal.ofReal (f n ω))) A :=
    esscher_finite_grid_stop_likelihood_history
      X θ hθ T (τn n) (grid n)
      (hgrid n) (fun s hs => hT n s hs)
      (fun s hs => hstop n s hs)
      A hA (fun s hs => hHistory n s hs)
  have hconst : Tendsto
      (fun n => (P.withDensity (fun ω => ENNReal.ofReal (f n ω))) A)
      atTop (𝓝 (QT A)) := by
    have heq : (fun n => (P.withDensity
        (fun ω => ENNReal.ofReal (f n ω))) A) =
        (fun _ : ℕ => QT A) := funext fun n => (hEach n).symm
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst hconv
