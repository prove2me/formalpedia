-- Prove2me | solution 1 for AvramDividend.Classical.stoppedMarkov_scale_ratio_upper_from_future_exit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:08:08.588289+00:00
-- url     : https://prove2.me/submissions/16a1be89-67fe-458f-a31a-7a01d8e5705e

import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Combine the upper Markov-factor estimate for killed records with a
    scale-ratio upper bound for the independent shifted exit reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A)
    (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward)
    (killedWeight : Ω → ℝ≥0∞) (ratio : ℝ≥0∞)
    (hRatio :
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) ≤ ratio)
    (hUpper : ∀ ω : Ω, killedWeight ω ≤
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0)) :
    (∫⁻ ω, killedWeight ω ∂P) ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      ratio := by
  calc
    (∫⁻ ω, killedWeight ω ∂P) ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) :=
      stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
        X τ hτ A hA hAfine hτfine discount hd reward hr
        killedWeight hUpper
    _ ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        ratio := by
          gcongr
