-- Prove2me | solution 1 for AvramDividend.Classical.chat08_named_upper_clock_eq_raw_infimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:15:07.891367+00:00
-- url     : https://prove2.me/submissions/cc3d7312-54fe-4240-b370-2257e439ea07

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The official strict passage clock is the indexed infimum used by the stopped-record grid lemmas. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (c : ℝ) (ω : Ω) :
    twoSidedExitUpTime X c ω =
      ⨅ (r : ℝ≥0) (_ : c < X.X r ω), (r : ℝ≥0∞) := by
  rfl
