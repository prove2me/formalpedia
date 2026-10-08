-- Prove2me | solution 1 for AvramDividend.Classical.laplace_integrated_remainder_kernel_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:37:05.341985+00:00
-- url     : https://prove2.me/submissions/d661779e-a604-4d58-a01b-4080e25e3b6c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-(s * t)) := by
  have hst : 0 ≤ s * t := mul_nonneg hs ht
  have hneg : -(s * t) ≤ 0 := neg_nonpos.mpr hst
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr hneg)
