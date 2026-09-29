-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_complex_left_clearance_standalone_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T18:26:32.850227+00:00
-- url     : https://prove2.me/submissions/82880d1b-db1e-4fd9-a497-0798082c34be

import Mathlib

theorem solution (n c r : ℝ) (z : ℂ)
    (hmargin : n + 1 / 4 ≤ c - r / 2) (hnorm : ‖z‖ = r) :
    n < (((c : ℂ) - (1 / 2 : ℂ) * z).re) := by
  have hRe := Complex.abs_re_le_norm z
  rw [hnorm] at hRe
  have hb := abs_le.mp hRe
  have hcoord : (((c : ℂ) - (1 / 2 : ℂ) * z).re) =
      c - z.re / 2 := by
    simp [Complex.sub_re, Complex.mul_re]
    ring
  rw [hcoord]
  nlinarith [hmargin, hb.2]
