-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_right_clearance_arith_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T18:05:52.252564+00:00
-- url     : https://prove2.me/submissions/609967f9-2ed2-44ec-8c18-9067e5b026f8

import Mathlib

theorem solution (n c r z : ℝ)
    (hmargin : n + 1 / 4 ≤ c - r / 2) (hz : -r ≤ z) :
    n < c + z / 2 := by
  linarith
