-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_original_killedRecord_fixedFuture_markov_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:31:38.96998+00:00
-- url     : https://prove2.me/submissions/9f3cb275-ea87-4b59-ab5f-d9214a1e4c78

import Theorems.Thm_AvramDividend_Classical_avram_ws01h_original_record_survival_stopped_history
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_rightCont_stopping_and_clock_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_measurable_of_equal_finite_clocks
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual unreflected lower-killed first upper record factors every
    nonnegative measurable full-future-path reward at a finite cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower b : ℝ) (N : ℝ≥0)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
    let A : Set Ω :=
      {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
      {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
    (∫⁻ ω, if ω ∈ A then
      discount (τ ω) *
        reward (fun u : ℝ≥0 => X.X (τ ω + u) ω - X.X (τ ω) ω)
      else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun u : ℝ≥0 => X.X u ω) ∂P) := by
  intro τ A
  obtain ⟨hτ, hτmeas⟩ :=
    firstRecord_capped_rightCont_stopping_and_clock_measurable X b N
  have hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A := by
    exact stoppedHistory_measurable_of_equal_finite_clocks
      (𝓕 := 𝓕.rightCont) _
      (firstRecord_truncation_stopping_rightCont X b N) _
      ((upperPassage_stopping_rightCont_filtration X b).min_const N)
      (fun ω => firstRecord_capped_coe_toNNReal_with_measure_import X b N ω) _
      (avram_ws01h_original_record_survival_stopped_history X lower b N)
  have hAfine : MeasurableSet A := by
    exact (chat03_upper_before_lower_passage_event_measurable X lower b).inter
      (measurableSet_le (upperPassage_measurable_from_stopping X b)
        measurable_const)
  convert levy_rightCont_finiteStopping_discountedFutureReward_factor
    X τ hτ A hA hAfine hτmeas discount hd reward hr
