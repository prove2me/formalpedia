-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_capped_clock_eq_uncapped_of_le_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:32:22.631626+00:00
-- url     : https://prove2.me/submissions/efa0b9c9-c3d6-4162-a742-1153f05573fb

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_coe_toNNReal_with_measure_import
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A first record reached by the cap has identical capped and uncapped clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0) (ω : Ω)
    (hbound : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)) :
    (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      twoSidedExitUpTime X b ω := by
  calc
    (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
        min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞) :=
      firstRecord_capped_coe_toNNReal_with_measure_import X b N ω
    _ = twoSidedExitUpTime X b ω := min_eq_left hbound
