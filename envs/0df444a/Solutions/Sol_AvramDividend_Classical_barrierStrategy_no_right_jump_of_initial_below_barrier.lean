-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_no_right_jump_of_initial_below_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T17:00:13.076298+00:00
-- url     : https://prove2.me/submissions/5c419e39-1882-4490-88ca-6e9b60b7b116

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Starting no higher than the barrier eliminates the initial lump
sum, so the barrier cumulative dividend path has no right jump anywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (t : ℝ≥0) :
    rightLimit (barrierStrategy X x a) t ω =
      barrierStrategy X x a t ω := by
  have hInc := barrierStrategy_right_increment_formula X x a ω t
  have hsub : x - a ≤ 0 := sub_nonpos.mpr hxa
  have hmax : max 0 (x - a) = 0 := max_eq_left hsub
  have hzero : (if t = 0 then max 0 (x - a) else 0) = 0 := by
    simp [hmax]
  rw [hzero] at hInc
  exact sub_eq_zero.mp hInc
