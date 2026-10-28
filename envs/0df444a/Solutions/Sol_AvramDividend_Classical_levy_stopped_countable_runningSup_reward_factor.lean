-- Prove2me | solution 1 for AvramDividend.Classical.levy_stopped_countable_runningSup_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:31:51.607131+00:00
-- url     : https://prove2.me/submissions/a7b8a39a-38a9-4c98-bcec-6d7fbe1beeac

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_countable_path_runningSup_increment_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

/-- Killed discounted countable-record rewards factor at a finite Lévy stopping clock. -/
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
    (times : ℕ → ℝ≥0) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      (⨆ n : ℕ, ENNReal.ofReal
        ((X.X (τ ω + times n) ω - X.X (τ ω) ω) -
          (X.X (τ ω + 0) ω - X.X (τ ω) ω)))
      else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, ⨆ n : ℕ,
        ENNReal.ofReal (X.X (times n) ω - X.X 0 ω) ∂P) := by
  let G : (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun f => ⨆ n : ℕ, ENNReal.ofReal (f (times n) - f 0)
  have hG : Measurable G :=
    countable_path_runningSup_increment_measurable times
  exact levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
    X τ hτ A hA hAfine hτfine discount hd G hG
