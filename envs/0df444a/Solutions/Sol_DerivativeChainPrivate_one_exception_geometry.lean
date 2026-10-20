-- Prove2me | solution 1 for DerivativeChainPrivate.one_exception_geometry
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:57:36.805011+00:00
-- url     : https://prove2.me/submissions/27a2982c-c12f-477b-b8f6-dbb2e91fd967

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a l r L R U V : ℝ)
    (hl : l ≤ a) (hr : a ≤ r) (hLR : L ≤ R)
    (hU : -1 ≤ U) (hl1 : -1 ≤ l) (hr1 : r ≤ 1) (hV : V ≤ 1) :
    min (a - l + |L - l| + L - U) (r - a + |R - r| + V - R) ≤ 3 := by
  by_cases hLl : L ≤ l
  · rw [abs_of_nonpos (sub_nonpos.mpr hLl)]
    exact (min_le_left _ _).trans (by linarith)
  by_cases hrR : r ≤ R
  · rw [abs_of_nonneg (sub_nonneg.mpr hrR)]
    exact (min_le_right _ _).trans (by linarith)
  · rw [abs_of_nonneg (by linarith : 0 ≤ L - l),
      abs_of_nonpos (by linarith : R - r ≤ 0)]
    have hminl := min_le_left (a - l + (L - l) + L - U)
      (r - a + -(R - r) + V - R)
    have hminr := min_le_right (a - l + (L - l) + L - U)
      (r - a + -(R - r) + V - R)
    linarith
