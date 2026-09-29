-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_complex_right_clearance_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T18:24:35.503333+00:00
-- url     : https://prove2.me/submissions/333b5713-3ca3-46f4-8318-875f20f8ed47

import Mathlib
import Theorems.Thm_BraidsLinksMCG_adjacent_left_clearance_arith_child_v1
import Theorems.Thm_BraidsLinksMCG_adjacent_right_clearance_arith_child_v1
open BraidsLinksMCG

theorem solution (n c r : ℝ) (z : ℂ)
    (hmargin : n + 1 / 4 ≤ c - r / 2) (hnorm : ‖z‖ = r) :
    n < (((c : ℂ) + (1 / 2 : ℂ) * z).re) := by
  have hRe := Complex.abs_re_le_norm z
  rw [hnorm] at hRe
  have hb := abs_le.mp hRe
  have hcoord : (((c : ℂ) + (1 / 2 : ℂ) * z).re) = c + z.re / 2 := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  rw [hcoord]
  nlinarith [hmargin, hb.1]
