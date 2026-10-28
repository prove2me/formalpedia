-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitUpTime_mono_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:22:02.485313+00:00
-- url     : https://prove2.me/submissions/1d1a47a0-2d72-45f3-8a15-95bd601fce76

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Increasing the upper crossing threshold cannot shorten the passage time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    twoSidedExitUpTime X a ω ≤ twoSidedExitUpTime X b ω := by
  unfold twoSidedExitUpTime
  refine le_iInf fun t => le_iInf fun ht => ?_
  exact iInf_le_of_le t
    (iInf_le_of_le (lt_of_le_of_lt hab ht) le_rfl)
