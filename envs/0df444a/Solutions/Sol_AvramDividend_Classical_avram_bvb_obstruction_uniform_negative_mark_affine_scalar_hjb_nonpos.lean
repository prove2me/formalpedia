-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_uniform_negative_mark_affine_scalar_hjb_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:52:45.661501+00:00
-- url     : https://prove2.me/submissions/5dbce467-d490-48ae-8abd-570cdb6b2603

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
theorem solution (y : ℝ) (hy : 0 < y) :
    (if y < 1 then -(3 / 2 : ℝ) * y + (1 / 2 : ℝ) * y ^ 2
     else -y) ≤ 0 := by
  split_ifs with h
  · have hprod : 0 ≤ y * (1 - y) :=
      mul_nonneg (le_of_lt hy) (sub_nonneg.mpr (le_of_lt h))
    nlinarith
  · linarith
