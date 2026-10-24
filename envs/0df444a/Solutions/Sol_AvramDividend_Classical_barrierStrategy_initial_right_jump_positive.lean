-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_right_jump_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:35:34.943826+00:00
-- url     : https://prove2.me/submissions/4ab3631f-8e11-461d-a1e6-c6aff0306460

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Initial surplus above the barrier produces a strictly positive right dividend jump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hax : a < x)
    (ω : Ω) :
    0 < rightLimit (barrierStrategy X x a) 0 ω -
        barrierStrategy X x a 0 ω := by
  have hp : 0 < x - a := sub_pos.mpr hax
  rw [barrierStrategy_right_increment_formula X x a ω 0]
  simpa [max_eq_right (le_of_lt hp)] using hp
