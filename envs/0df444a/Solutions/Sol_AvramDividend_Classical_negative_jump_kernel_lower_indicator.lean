-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_kernel_lower_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:30:30.293991+00:00
-- url     : https://prove2.me/submissions/1198ecf0-1088-490f-a81d-860808f071db

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (θ y : ℝ) (hy : y < 0) :
    (Ioo (-1 : ℝ) 0).indicator
        (fun z : ℝ => Real.exp (θ * z) - 1 - θ * z) y -
      (Iic (-1 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y ≤
      Real.exp (θ * y) - 1 -
        θ * y * (Ioo (-1 : ℝ) 1).indicator
          (fun _ : ℝ => (1 : ℝ)) y := by
  by_cases hsmall : -1 < y
  · have hs : y ∈ Ioo (-1 : ℝ) 0 := ⟨hsmall, hy⟩
    have hnotL : y ∉ Iic (-1 : ℝ) := not_le_of_gt hsmall
    have hmid : y ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hnotL,
      Set.indicator_of_mem hmid, sub_zero, mul_one, le_refl]
  · have hge : y ≤ -1 := le_of_not_gt hsmall
    have hbig : y ∈ Iic (-1 : ℝ) := hge
    have hnotS : y ∉ Ioo (-1 : ℝ) 0 := by
      intro h
      exact (not_lt_of_ge hge) h.1
    have hnotM : y ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge hge) h.1
    simp only [Set.indicator_of_notMem hnotS, Set.indicator_of_mem hbig,
      Set.indicator_of_notMem hnotM, mul_zero, sub_zero]
    linarith [Real.exp_pos (θ * y)]
