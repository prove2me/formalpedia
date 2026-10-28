-- Prove2me | solution 2 for AvramDividend.Classical.firstRecord_capped_coe_toNNReal_with_measure_import
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:59:55.468301+00:00
-- url     : https://prove2.me/submissions/ee4176d0-bdb5-4c02-8417-e472b8fc6224

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-! A finite cap gives a genuinely finite extended first-record clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (N : ℝ≥0) (ω : Ω) :
    (((min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞) := by
  apply ENNReal.coe_toNNReal
  exact ne_of_lt
    (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top)