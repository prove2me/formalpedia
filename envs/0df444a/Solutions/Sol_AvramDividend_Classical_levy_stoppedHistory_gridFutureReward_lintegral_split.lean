-- Prove2me | solution 1 for AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_lintegral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:19:24.666992+00:00
-- url     : https://prove2.me/submissions/99f8c216-1b13-4489-96e6-7f400ca72f1f

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_lintegral_decomposition
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_fibre_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- The full stopped-grid Lévy future payoff integrates fibrewise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
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
      ∑ s ∈ grid, ∫⁻ ω,
        Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
          (fun ω' => g (fun t : ℝ≥0 =>
            X.X (s + t) ω' - X.X s ω')) ω ∂P := by
  apply finiteGrid_stoppedReward_lintegral_decomposition
    P (τn n) A grid hgrid
    (fun s ω => g (fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω))
  intro s hs
  exact levy_stoppedHistory_gridFutureReward_fibre_measurable
    X τ A hA τn habove hfibres n s g hg