-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_strict_negative_cutoff_mark_weight_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:19:47.309239+00:00
-- url     : https://prove2.me/submissions/a3af0ce6-830c-415f-b5a8-3d9c3961d861

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution (k : ℕ) :
    Measurable (fun z : ℝ =>
      if z < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-z) else 0) := by
  apply Measurable.ite measurableSet_Iio
  · exact ENNReal.measurable_ofReal.comp measurable_neg
  · exact measurable_const
