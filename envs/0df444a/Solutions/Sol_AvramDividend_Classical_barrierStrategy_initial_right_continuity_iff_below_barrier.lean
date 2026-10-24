-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_initial_right_continuity_iff_below_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T17:08:03.047028+00:00
-- url     : https://prove2.me/submissions/013548b3-0c79-4716-9126-11a38a49b35b

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The only possible right jump at the origin is the initial barrier excess. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω) :
    (rightLimit (barrierStrategy X x a) 0 ω =
      barrierStrategy X x a 0 ω) ↔ x ≤ a := by
  constructor
  · intro hcont
    have hInc := barrierStrategy_right_increment_formula X x a ω 0
    have hzero :
        rightLimit (barrierStrategy X x a) 0 ω -
          barrierStrategy X x a 0 ω = 0 := sub_eq_zero.mpr hcont
    have hm : max 0 (x - a) = 0 := by
      simpa [hzero] using hInc.symm
    have hle : x - a ≤ (0 : ℝ) := by
      have hbound : x - a ≤ max (0 : ℝ) (x - a) := le_max_right _ _
      simpa [hm] using hbound
    exact sub_nonpos.mp hle
  · intro hxa
    exact barrierStrategy_no_right_jump_of_initial_below_barrier X x a hxa ω 0
