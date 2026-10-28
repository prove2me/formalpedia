-- Prove2me | solution 1 for AvramDividend.Classical.stoppedMarkov_pointwise_record_lower_to_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:59:58.130987+00:00
-- url     : https://prove2.me/submissions/019d6b0d-abca-447d-88d4-633a098d19c6

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A pointwise surviving-record reward lower bound passes through the
stopped-history strong-Markov factorisation into an expectation lower bound. -/
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
    (killedWeight : Ω → ℝ≥0∞)
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0) ≤ killedWeight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) ≤
        (∫⁻ ω, killedWeight ω ∂P) := by
  calc
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0 ∂P) :=
      (levy_finiteStopping_killedDiscount_futureReward_factor
        X τ hτ A hA hAfine hτfine discount hd reward hr).symm
    _ ≤ (∫⁻ ω, killedWeight ω ∂P) := lintegral_mono hLower