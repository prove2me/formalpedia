-- Prove2me | solution 1 for AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:54:59.840125+00:00
-- url     : https://prove2.me/submissions/ec14c303-e38a-4084-ba16-a1dac7f15a4f

import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedReward_fibre_decomposition
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_fibre_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- A full future payoff at a finite adapted stopping grid is measurable. -/
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
    Measurable (Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τn n ω' + t) ω' - X.X (τn n ω') ω'))) := by
  have hsum : Measurable (fun ω : Ω =>
      ∑ s ∈ grid,
        Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
          (fun ω' => g (fun t : ℝ≥0 =>
            X.X (s + t) ω' - X.X s ω')) ω) := by
    apply Finset.measurable_sum
    intro s hs
    exact levy_stoppedHistory_gridFutureReward_fibre_measurable
      X τ A hA τn habove hfibres n s g hg
  convert hsum using 1
  funext ω
  exact (finiteGrid_stoppedReward_fibre_decomposition
    (τn n) A grid hgrid
    (fun s ω' => g (fun t : ℝ≥0 =>
      X.X (s + t) ω' - X.X s ω')) ω).symm

