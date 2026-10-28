-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_killedDiscount_futureReward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:49:28.098593+00:00
-- url     : https://prove2.me/submissions/81a91dcf-c576-46e1-80f5-526c06b24122

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_finiteStopping_clock_measurable_stoppedSigma
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_historyWeight_futureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Killed stopping-time discounts separate from post-stopping Lévy rewards. -/
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
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  classical
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  let pastWeight : Ω → ℝ≥0∞ := fun ω =>
    if ω ∈ A then discount (τ ω) else 0
  have hClock : Measurable[hstop.measurableSpace] τ := by
    simpa only [hstop] using
      (finiteStopping_clock_measurable_stoppedSigma τ hτ)
  have hp : Measurable pastWeight :=
    Measurable.ite hAfine (hd.comp hτfine) measurable_const
  have hpPast : Measurable[hstop.measurableSpace] pastWeight :=
    Measurable.ite hA (hd.comp hClock) measurable_const
  have hMain :=
    levy_finiteStopping_historyWeight_futureReward_factor
      X τ hτ pastWeight hp hpPast reward hr
  simpa only [pastWeight, ite_mul, zero_mul] using hMain
