-- Prove2me | solution 1 for AvramDividend.Classical.stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:14:30.840667+00:00
-- url     : https://prove2.me/submissions/3553e23f-25c4-4d2b-86c4-b27da89c9838

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

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
    (killedWeight : Ω → ℝ≥0∞)
    (hUpper : ∀ ω : Ω, killedWeight ω ≤
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0)) :
    (∫⁻ ω, killedWeight ω ∂P) ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  have hfactor :=
    levy_rightCont_finiteStopping_discountedFutureReward_factor
      X τ hτ A hA hAfine hτfine discount hd reward hr
  rw [← hfactor]
  exact lintegral_mono hUpper
