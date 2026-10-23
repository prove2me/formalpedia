-- Prove2me | solution 1 for AvramDividend.Classical.corrected_upperfirst_exit_lintegral_le_unrestricted_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:59:03.74499+00:00
-- url     : https://prove2.me/submissions/2c0dba32-9bf7-46f2-ab25-af09d99406b0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) :
    twoSidedExitExpectationCorrected X q a x ≤
      ∫⁻ ω, if twoSidedExitUpTimeCorrected X (a - x) ω < (⊤ : ℝ≥0∞)
        then ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTimeCorrected X (a - x) ω))))
        else 0 ∂P := by
  unfold twoSidedExitExpectationCorrected
  apply lintegral_mono
  intro ω
  by_cases h : twoSidedExitUpTimeCorrected X (a - x) ω <
      twoSidedExitDownTimeCorrected X (-x) ω
  · have hu : twoSidedExitUpTimeCorrected X (a - x) ω < (⊤ : ℝ≥0∞) :=
      lt_of_lt_of_le h le_top
    simp only [if_pos h, if_pos hu]
    exact le_refl _
  · simp only [if_neg h]
    exact bot_le
