-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_times_eq_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:26:05.353187+00:00
-- url     : https://prove2.me/submissions/cc48d622-e896-479b-9861-651279143f55

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The two strict upward clocks and the two strict downward clocks
coincide pointwise, including zero-time and infinity cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b c : ℝ) (ω : Ω) :
    twoSidedExitUpTime X b ω = twoSidedExitUpTimeCorrected X b ω ∧
      twoSidedExitDownTime X c ω = twoSidedExitDownTimeCorrected X c ω := by
  constructor <;> rfl
