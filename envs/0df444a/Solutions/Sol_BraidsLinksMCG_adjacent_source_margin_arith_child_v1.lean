-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_source_margin_arith_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T17:16:07.520794+00:00
-- url     : https://prove2.me/submissions/94fcc988-f7d0-4efc-a560-68596a88d891

import Mathlib

theorem solution (n : ℕ) (r : ℝ) (z : ℂ)
    (hr : r ≤ 1) (hz : -(1 / 2 : ℝ) ≤ z.re) :
    (n : ℝ) + 1 / 4 ≤ (n : ℝ) + 1 + (1 / 2 : ℝ) * z.re - r / 2 := by
  nlinarith
