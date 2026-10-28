-- Prove2me | solution 1 for AvramDividend.Classical.levy_stoppedHistory_upperGrid_futureReward_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:13:00.394803+00:00
-- url     : https://prove2.me/submissions/040ac842-8b96-41ef-a8b1-93d0f81e8c64

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteGrid_stoppedEvent_stationaryFuture_reward
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Finite upper-rounded stopped-history fibres restart with the original Lévy path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ι → ℝ≥0)
    (f : ι → ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∑ i, ∫⁻ ω,
      f i (Set.indicator (A ∩ {ω : Ω | τn n ω = s i})
          (fun _ : Ω => (1 : ℝ)) ω,
        (fun t : ℝ≥0 => X.X (s i + t) ω - X.X (s i) ω)) ∂P) =
      ∑ i, ∫⁻ h, ∫⁻ y, f i (h, y)
        ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
        ∂(Measure.map
          (Set.indicator (A ∩ {ω : Ω | τn n ω = s i})
            (fun _ : Ω => (1 : ℝ))) P) := by
  exact levy_finiteGrid_stoppedEvent_stationaryFuture_reward X
    (fun u => levy_shiftedFuturePath_stationary_law X u)
    s (fun i => A ∩ {ω : Ω | τn n ω = s i})
    (fun i => stoppedEvent_upperGridFibre_measurable
      τ A hA τn habove hfibres n (s i)) f hf
