-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_upper_first_preserves_lower_survival_through_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:09:31.220303+00:00
-- url     : https://prove2.me/submissions/6381c2af-9949-41d3-87c7-b052f5424a3b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- An original path whose strict upper first record precedes lower ruin
cannot breach the lower reserve barrier at any preceding observation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (ω : Ω) (s : ℝ≥0)
    (hfirst : twoSidedExitUpTime X b ω <
      twoSidedExitDownTime X (-x) ω)
    (hbefore : (s : ℝ≥0∞) ≤ twoSidedExitUpTime X b ω) :
    0 ≤ x + X.X s ω := by
  by_contra hneg
  have hg : X.X s ω < -x := by linarith
  have hd :
      twoSidedExitDownTime X (-x) ω ≤ (s : ℝ≥0∞) :=
    twoSidedExitDownTime_le_of_strict_lower_gap_observed
      X x ω s hg
  exact (not_lt_of_ge (hd.trans hbefore)) hfirst
