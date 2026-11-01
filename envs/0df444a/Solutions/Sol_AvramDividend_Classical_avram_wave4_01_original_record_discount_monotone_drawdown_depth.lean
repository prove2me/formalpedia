-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_monotone_drawdown_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:25:48.640742+00:00
-- url     : https://prove2.me/submissions/bf4ccac8-49ea-43e5-a3ef-a6d5b30f80fc

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Mathlib.Analysis.Complex.Exponential

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine killed first-record discount increases when the actual
reflected drawdown ruin depth is enlarged. No scale function is required. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q h a b : ℝ) (hab : a ≤ b) :
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X b ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P) := by
  classical
  apply lintegral_mono
  intro ω
  by_cases hrecord :
      twoSidedExitUpTime X h ω < barrierRuinTime X a ω
  · have hrecordLarge :
        twoSidedExitUpTime X h ω < barrierRuinTime X b ω :=
      lt_of_lt_of_le hrecord
        (barrierRuinTime_mono_barrier X a b hab ω)
    simp only [if_pos hrecord, if_pos hrecordLarge, le_refl]
  · simp only [if_neg hrecord]
    exact bot_le
