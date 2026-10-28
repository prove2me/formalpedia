-- Prove2me | solution 1 for AvramDividend.Classical.stoppedMarkov_scale_ratio_lower_rightCont_of_exit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:07:06.212984+00:00
-- url     : https://prove2.me/submissions/9a2c96f3-91c0-4da2-9d43-8674d7aead35

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Discounted killed-record expectation dominates the capped-record mass
    times a scale-ratio lower estimate of the fresh two-sided-exit payoff. -/
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
    _ =
      (∫⁻ ω,
        if ω ∈ A then discount (τ ω) *
          reward (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0 ∂P) :=
      (levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
        X τ hτ A hA hAfine hτfine discount hd reward hr).symm
    _ ≤ (∫⁻ ω, killedWeight ω ∂P) := lintegral_mono hLower
