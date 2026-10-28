-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_firstRecord_uncensored_discountedFutureReward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:23:09.380767+00:00
-- url     : https://prove2.me/submissions/ac39c3af-d715-4031-b379-51ba6c4e544a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a capped strict first Lévy record, an uncensored record event and
an arbitrary measurable discount of the stopping age factor from the
whole shifted future-path reward. This uses the true right-continuous
stopped history, with no unrelated lower-ruin requirement. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω := {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       reward (fun t : ℝ≥0 =>
         X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
         (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  dsimp only
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω := {ω : Ω |
    twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
  have hτstop : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s} :=
    firstRecord_truncation_stopping_rightCont X b N
  have hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτstop).measurableSpace] A :=
    avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory X b N
  have hAfine : MeasurableSet A :=
    (isStoppingTime_withTop_of_le_events τ hτstop).measurableSpace_le A hA
  have hτfine : Measurable τ :=
    firstRecord_truncation_clock_measurable X b N
  simpa only [τ, A] using
    (levy_rightCont_finiteStopping_discountedFutureReward_factor
      X τ hτstop A hA hAfine hτfine discount hd reward hr)
