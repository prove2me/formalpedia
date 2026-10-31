-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_record_discount_antitone_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:19:54.676686+00:00
-- url     : https://prove2.me/submissions/e2ab5e3d-39df-434f-a116-828d8dc52a13

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual discounted first-record survival decreases as the upward level increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q b c : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hb : 0 ≤ b) (hbc : b ≤ c) :
    (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
    else 0 ∂P) := by
  apply lintegral_mono
  intro ω
  have hclock : twoSidedExitUpTime X b ω ≤ twoSidedExitUpTime X c ω :=
    twoSidedExitUpTime_mono_threshold X b c hbc ω
  by_cases hc : twoSidedExitUpTime X c ω < barrierRuinTime X a ω
  · have hbefore : twoSidedExitUpTime X b ω < barrierRuinTime X a ω :=
      lt_of_le_of_lt hclock hc
    simp only [if_pos hc, if_pos hbefore]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have ht : (twoSidedExitUpTime X b ω).toReal ≤
        (twoSidedExitUpTime X c ω).toReal :=
      ENNReal.toReal_mono (ne_top_of_lt hc) hclock
    have hmul := mul_le_mul_of_nonneg_left ht hq.le
    linarith
  · simp only [if_neg hc]
    exact bot_le
