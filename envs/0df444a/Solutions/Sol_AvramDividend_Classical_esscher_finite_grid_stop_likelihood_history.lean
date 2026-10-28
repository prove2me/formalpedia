-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_stop_likelihood_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:50:50.222549+00:00
-- url     : https://prove2.me/submissions/ec971b1f-483a-4d6b-8e15-6a6aa7d77bd8

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-- The density at a finite-valued stopping time identifies the
finite-terminal Esscher law on stopped-history events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s})) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) A := by
  let QT : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let Qstop : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
    (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))
  have hfib : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s} := by
    intro s hs
    exact 𝓕.le s _ (hstop s hs)
  have hcell : ∀ s ∈ grid,
      QT (A ∩ {ω : Ω | τ ω = s}) =
        Qstop (A ∩ {ω : Ω | τ ω = s}) := by
    intro s hs
    let C : Set Ω := A ∩ {ω : Ω | τ ω = s}
    have hC : MeasurableSet C := 𝓕.le s _ (hHistory s hs)
    calc
      QT C = (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) C := by
            exact (chat04_esscher_finite_horizon_laws_consistent_on_past_events
              X θ hθ s T (hT s hs) C (hHistory s hs)).symm
      _ = Qstop C := by
        dsimp [Qstop]
        rw [withDensity_apply _ hC, withDensity_apply _ hC]
        rw [← lintegral_indicator hC, ← lintegral_indicator hC]
        apply lintegral_congr
        intro ω
        by_cases hw : ω ∈ C
        · have hτ : τ ω = s := hw.2
          simp [Set.indicator_of_mem hw, hτ]
        · simp [Set.indicator_of_notMem hw]
  change QT A = Qstop A
  calc
    QT A = ∑ s ∈ grid, QT (A ∩ {ω : Ω | τ ω = s}) :=
      finiteGrid_stoppedEvent_measure_partition QT τ A grid hgrid hA hfib
    _ = ∑ s ∈ grid, Qstop (A ∩ {ω : Ω | τ ω = s}) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hcell s hs
    _ = Qstop A :=
      (finiteGrid_stoppedEvent_measure_partition Qstop τ A grid hgrid hA hfib).symm
