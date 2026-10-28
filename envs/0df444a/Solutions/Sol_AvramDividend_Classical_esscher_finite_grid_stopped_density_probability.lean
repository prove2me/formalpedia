-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stopped_density_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:58:30.413041+00:00
-- url     : https://prove2.me/submissions/1a4f427a-5a2b-4706-bc35-e30dc6823467

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Optional sampling on a finite grid preserves total unit mass
of the compensated exponential Esscher likelihood. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s}) :
    IsProbabilityMeasure (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by
  let QT : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let Qstop : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
    (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))
  haveI : IsProbabilityMeasure QT :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  have hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (Set.univ ∩ {ω : Ω | τ ω = s}) := by
    intro s hs
    simpa using hstop s hs
  have hEq : QT Set.univ = Qstop Set.univ := by
    exact esscher_finite_grid_stop_likelihood_history X θ hθ T τ grid
      hgrid hT hstop Set.univ MeasurableSet.univ hHistory
  refine ⟨?_⟩
  exact hEq.symm.trans (measure_univ : QT Set.univ = 1)
