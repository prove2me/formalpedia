-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_antitone_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:21:59.207588+00:00
-- url     : https://prove2.me/submissions/ebc6f18c-9544-497c-9d50-436f5376c26b

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Increasing the lower crossing threshold can only shorten the passage time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    twoSidedExitDownTime X b ω ≤ twoSidedExitDownTime X a ω := by
  unfold twoSidedExitDownTime
  refine le_iInf fun t => le_iInf fun ht => ?_
  exact iInf_le_of_le t
    (iInf_le_of_le (lt_of_lt_of_le ht hab) le_rfl)
