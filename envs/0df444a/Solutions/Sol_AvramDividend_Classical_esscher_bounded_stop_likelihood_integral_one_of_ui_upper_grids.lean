-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:48:36.883872+00:00
-- url     : https://prove2.me/submissions/574be207-aa50-43e7-ab1c-a4949b07eae6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_integral_mass_one_of_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability
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
    (hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by
  let f : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)
  let g : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)
  have hlimf : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) :=
    Filter.Eventually.of_forall
      (esscher_stopped_likelihood_tendsto_of_right_approximation
        X θ hθ τ τn hlim habove)
  have hmass (n : ℕ) : (∫ ω, f n ω ∂P) = (1 : ℝ) := by
    haveI : IsProbabilityMeasure
        (P.withDensity (fun ω : Ω => ENNReal.ofReal (f n ω))) :=
      esscher_finite_grid_stopped_density_probability
        X θ hθ T (τn n) (grid n)
        (hgrid n)
        (fun s hs => hT n s hs)
        (fun s hs => hstop n s hs)
    have hu : (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (f n ω))) Set.univ = 1 := measure_univ
    have hlin : (∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) = 1 := by
      rw [withDensity_apply _ MeasurableSet.univ] at hu
      simpa using hu
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
      (hUI.1 n)]
    rw [hlin]
    norm_num
  exact uniformIntegrable_integral_mass_one_of_ae_tendsto P f g hUI hlimf hmass
