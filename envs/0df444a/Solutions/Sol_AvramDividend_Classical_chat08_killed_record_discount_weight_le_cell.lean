-- Prove2me | solution 1 for AvramDividend.Classical.chat08_killed_record_discount_weight_le_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:19:22.721234+00:00
-- url     : https://prove2.me/submissions/95ac1340-bfbe-4981-8757-d7e41af1adfa

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! Killed first-record discounted payments are uniformly bounded by the un-discounted cell mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c q h : ℝ)
    (hq : 0 ≤ q) (hh : 0 ≤ h) (ω : Ω) :
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (h * Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0) ≤ ENNReal.ofReal h := by
  split_ifs with hpass
  · have htime : 0 ≤ (twoSidedExitUpTime X c ω).toReal := ENNReal.toReal_nonneg
    have hqt : 0 ≤ q * (twoSidedExitUpTime X c ω).toReal :=
      mul_nonneg hq htime
    have hexp : Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
    have hmul :
        h * Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)) ≤ h := by
      simpa using mul_le_mul_of_nonneg_left hexp hh
    exact ENNReal.ofReal_le_ofReal hmul
  · exact bot_le
