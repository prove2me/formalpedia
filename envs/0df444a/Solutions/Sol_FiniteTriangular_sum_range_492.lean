-- Prove2me | solution 1 for FiniteTriangular.sum_range_492
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:18:58.768646+00:00
-- url     : https://prove2.me/submissions/e7abe865-e06c-462d-a491-677eb4f4a69c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 492, k = 120786 := by
  rw [sum_range_id]
