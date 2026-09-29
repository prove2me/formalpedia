-- Prove2me | solution 1 for BraidsLinksMCG.adjacentCenter0_re_child_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T16:42:34.076332+00:00
-- url     : https://prove2.me/submissions/0a9266cb-9e21-48f9-9876-de282c336360

import Mathlib

theorem solution (n : ℕ) (w : ℂ) :
    (((n : ℝ) + 1 : ℂ) + (1 / 2 : ℂ) * w).re =
      (n : ℝ) + 1 + (1 / 2 : ℝ) * w.re := by
  simp [Complex.add_re, Complex.mul_re]
