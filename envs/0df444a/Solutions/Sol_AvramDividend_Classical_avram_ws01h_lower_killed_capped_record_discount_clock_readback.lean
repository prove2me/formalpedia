-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_lower_killed_capped_record_discount_clock_readback
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:35:29.389004+00:00
-- url     : https://prove2.me/submissions/6df0f9c2-b953-4ef8-a959-0f3b71b5335e

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Inside the actual lower-killed capped upper-record event, the
discount clock is the uncapped genuine source upper first-passage age. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b lower : ℝ) (N : ℝ≥0) (F : ℝ≥0 → ℝ≥0∞) :
    (∫⁻ ω, if twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      F (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
      else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      F (twoSidedExitUpTime X b ω).toNNReal else 0 ∂P) := by
  apply lintegral_congr
  intro ω
  by_cases hA : twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)
  · have htime :
        (min (twoSidedExitUpTime X b ω)
          (N : ℝ≥0∞)).toNNReal =
        (twoSidedExitUpTime X b ω).toNNReal := by
      have h := congrArg ENNReal.toNNReal
        (firstRecord_capped_clock_eq_uncapped_of_le_horizon
          X b N ω hA.2)
      simpa only [ENNReal.toNNReal_coe] using h
    simp only [if_pos hA, htime]
  · simp only [if_neg hA]
