-- Prove2me | solution 1 for AvramDividend.Classical.chat04_twoSidedExitExpectation_eq_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:03:34.683539+00:00
-- url     : https://prove2.me/submissions/18557636-06d5-4629-82f4-008b52d082f8

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The original and corrected killed exit transforms unfold to the same strict
upcrossing, strict downcrossing, and discounted reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) :
    twoSidedExitExpectation X q a x =
      twoSidedExitExpectationCorrected X q a x := by
  rfl
