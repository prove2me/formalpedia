-- Prove2me | solution 1 for AvramDividend.Classical.levy_upperGrid_stoppedHistory_scalar_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:57:39.993458+00:00
-- url     : https://prove2.me/submissions/ddfc4758-705b-4427-9553-88655978eb09

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_lintegral_split
import Theorems.Thm_AvramDividend_Classical_levy_upperGrid_fibre_futureReward_scalar_factor
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- The finite-grid scalar strong-Markov formula for every measurable stopped-history event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hAm : MeasurableSet A)
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τn n ω ∈ grid)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τn n ω' + t) ω' - X.X (τn n ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  let c : ℝ≥0∞ := ∫⁻ y, g y ∂(Measure.map
    (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
  have hsplit := levy_stoppedHistory_gridFutureReward_lintegral_split
    X τ A hA τn habove hfibres n grid hgrid g hg
  have hfactor :
      (∑ s ∈ grid, ∫⁻ ω,
        Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
          (fun ω' => g (fun t : ℝ≥0 =>
            X.X (s + t) ω' - X.X s ω')) ω ∂P) =
      ∑ s ∈ grid, P (A ∩ {ω : Ω | τn n ω = s}) * c := by
    apply Finset.sum_congr rfl
    intro s hs
    exact levy_upperGrid_fibre_futureReward_scalar_factor
      X τ A hA τn habove hfibres n s g hg
  have hmass := finiteGrid_stoppedEvent_measure_partition
    P (τn n) A grid hgrid hAm (by
      intro s hs
      exact (𝓕.le s {ω : Ω | τn n ω = s}) (hfibres n s))
  calc
    _ = ∑ s ∈ grid, ∫⁻ ω,
      Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
        (fun ω' => g (fun t : ℝ≥0 =>
          X.X (s + t) ω' - X.X s ω')) ω ∂P := hsplit
    _ = ∑ s ∈ grid, P (A ∩ {ω : Ω | τn n ω = s}) * c := hfactor
    _ = (∑ s ∈ grid, P (A ∩ {ω : Ω | τn n ω = s})) * c := by
      rw [Finset.sum_mul]
    _ = P A * c := by rw [hmass]

