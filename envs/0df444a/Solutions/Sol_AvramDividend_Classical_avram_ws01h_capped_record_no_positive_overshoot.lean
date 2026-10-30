-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_capped_record_no_positive_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:18:27.608264+00:00
-- url     : https://prove2.me/submissions/b7f130f0-b473-4813-ac4f-9effb9aa194a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b)
    (N : ℝ≥0) (ω : Ω)
    (hhit : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    X.X ((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal) ω = b := by
  apply firstUpcrossing_value_eq_threshold X b hb ω
  simpa only [twoSidedExitUpTime] using
    (firstRecord_capped_clock_eq_uncapped_of_le_horizon X b N ω hhit)
