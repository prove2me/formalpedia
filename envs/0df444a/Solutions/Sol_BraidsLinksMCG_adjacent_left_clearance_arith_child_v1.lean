-- Prove2me | solution 1 for BraidsLinksMCG.adjacent_left_clearance_arith_child_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T18:05:38.019072+00:00
-- url     : https://prove2.me/submissions/0d927d23-02f7-429a-80c9-945b582747ae

import Mathlib

theorem solution (n c r z : ℝ)
    (hmargin : n + 1 / 4 ≤ c - r / 2) (hz : z ≤ r) :
    n < c - z / 2 := by
  linarith
