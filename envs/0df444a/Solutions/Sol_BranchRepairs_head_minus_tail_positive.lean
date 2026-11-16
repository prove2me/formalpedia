-- Prove2me | solution 1 for BranchRepairs.head_minus_tail_positive
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:29:52.668207+00:00
-- url     : https://prove2.me/submissions/3220dc60-384c-4ff1-af2c-d7d252b685b5

import Mathlib
open Filter Topology

theorem solution (head tail K : ℝ)
    (hh : 0 < head) (ht : tail < head/2) (hk : head-tail ≤ K) :
    head/2 < K := by linarith
