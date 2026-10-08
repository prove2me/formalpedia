-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_kernel_upper_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:39:00.996586+00:00
-- url     : https://prove2.me/submissions/a32c4dd4-e7be-4cc5-95aa-9def4347f292

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y ≤
      (Ioo (-1 : ℝ) 0).indicator
        (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) y := by
  by_cases hsmall : -1 < y
  · have hs : y ∈ Ioo (-1 : ℝ) 0 := ⟨hsmall, hy⟩
    have hmid : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    simp only [Set.indicator_of_mem hs, Set.indicator_of_mem hmid,
      mul_one, le_refl]
  · have hge : y ≤ -1 := le_of_not_gt hsmall
    have hnotS : y ∉ Ioo (-1 : ℝ) 0 := by
      intro h
      exact (not_lt_of_ge hge) h.1
    have hnotM : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge hge) h.1
    have hθy : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
    have he : Real.exp (θ * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr hθy
    simp only [Set.indicator_of_notMem hnotS,
      Set.indicator_of_notMem hnotM, mul_zero, sub_zero]
    linarith
