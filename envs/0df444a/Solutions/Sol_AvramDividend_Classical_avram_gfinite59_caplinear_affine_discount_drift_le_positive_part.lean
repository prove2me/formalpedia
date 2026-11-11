-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:19:11.022223+00:00
-- url     : https://prove2.me/submissions/0726862a-10a3-46bd-8e49-cd0060a5d7a9

import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem solution
    (c q wb b y : ℝ) (hq : 0 ≤ q)
    (hwb : 0 ≤ wb) (hby : b ≤ y) :
    c - q * (wb + (y - b)) ≤ max c 0 :=
  le_trans
    (sub_le_self c (mul_nonneg hq (add_nonneg hwb (sub_nonneg.mpr hby))))
    (le_max_left c 0)
