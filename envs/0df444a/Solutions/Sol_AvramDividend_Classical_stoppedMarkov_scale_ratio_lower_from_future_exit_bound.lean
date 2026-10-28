-- Prove2me | solution 1 for AvramDividend.Classical.stoppedMarkov_scale_ratio_lower_from_future_exit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:07:37.53009+00:00
-- url     : https://prove2.me/submissions/9ee4595d-0d51-4793-acbd-e0008dd77fd0

import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_lower_to_expectation
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Combine a scale-ratio bound on a fresh exit reward with strong-Markov
    domination of the killed next-record payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A)
    (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward)
    (killedWeight : Ω → ℝ≥0∞) (ratio : ℝ≥0∞)
    (hRatio : ratio ≤
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P))
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0) ≤ killedWeight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      ratio ≤ (∫⁻ ω, killedWeight ω ∂P) := by
  calc
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        ratio ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          gcongr
    _ ≤ (∫⁻ ω, killedWeight ω ∂P) :=
      stoppedMarkov_pointwise_record_lower_to_expectation
        X τ hτ A hA hAfine hτfine discount hd reward hr
        killedWeight hLower
