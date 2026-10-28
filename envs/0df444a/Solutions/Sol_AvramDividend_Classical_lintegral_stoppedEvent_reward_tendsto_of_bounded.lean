-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_stoppedEvent_reward_tendsto_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:57:28.549988+00:00
-- url     : https://prove2.me/submissions/25fe3dd8-365c-44dd-b26d-663f8849deff

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Bounded stopped-history rewards converge in expectation along pointwise stopping grids. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (f : ℕ → Ω → ℝ≥0∞) (fLim : Ω → ℝ≥0∞)
    (hf : ∀ n, Measurable (Set.indicator A (f n)))
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (nhds (fLim ω)))
    (C : ℝ≥0∞) (hbound : ∀ n ω, f n ω ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    Tendsto
      (fun n => ∫⁻ ω, Set.indicator A (f n) ω ∂P)
      atTop
      (nhds (∫⁻ ω, Set.indicator A fLim ω ∂P)) := by
  refine tendsto_lintegral_of_dominated_convergence
    (μ := P) (fun _ : Ω => C) hf ?_ hfin ?_
  · intro n
    filter_upwards [] with ω
    by_cases hω : ω ∈ A
    · simpa [Set.indicator, hω] using hbound n ω
    · simp [Set.indicator, hω]
  · filter_upwards [] with ω
    by_cases hω : ω ∈ A
    · simpa [Set.indicator, hω] using hlim ω
    · simp [Set.indicator, hω]

