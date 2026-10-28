-- Prove2me | solution 1 for AvramDividend.Classical.levy_rightCont_finiteStopping_discountedFutureReward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:03:33.638159+00:00
-- url     : https://prove2.me/submissions/f7d7d7ea-792d-4879-8dd3-db83dc499ca9

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

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
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  obtain ⟨Y, hY, _, _, _⟩ := levy_rightCont_process X
  have hfact := levy_finiteStopping_killedDiscount_futureReward_factor
    Y τ hτ A hA hAfine hτfine discount hd reward hr
  simpa only [hY] using hfact
