-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_firstRecord_strict_upcrossing_stoppedHistory
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:58:39.288996+00:00
-- url     : https://prove2.me/submissions/1b52e563-1d40-4b13-8fa2-ef31bb8eea15

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The event that the genuine strict upcrossing occurs before the cap
is observable at the capped first-record stopping time itself. This
allows survival-clock regeneration to retain the uncensored event
without introducing an extraneous lower-ruin restriction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) :
    MeasurableSet[
      (isStoppingTime_withTop_of_le_events
        (fun ω : Ω =>
          (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
        (firstRecord_truncation_stopping_rightCont X b N)).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)} := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => (τ ω : ℝ≥0∞)) :=
    isStoppingTime_withTop_of_le_events τ
      (firstRecord_truncation_stopping_rightCont X b N)
  have hEq :
      {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)} =
      {ω : Ω | (τ ω : ℝ≥0∞) < (N : ℝ≥0∞)} := by
    ext ω
    change twoSidedExitUpTime X b ω < (N : ℝ≥0∞) ↔
      (((min (twoSidedExitUpTime X b ω)
        (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) < (N : ℝ≥0∞)
    rw [firstRecord_capped_coe_toNNReal_with_measure_import X b N ω]
    simp only [min_lt_iff, lt_irrefl, or_false]
  rw [hEq]
  exact hStop.measurableSet_lt' N
