-- Prove2me | solution 1 for FiniteTriangular.sum_range_666
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:23.166778+00:00
-- url     : https://prove2.me/submissions/0c49bac4-d671-46fb-a290-e9494eb19fce

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 666, k = 221445 := by
  rw [sum_range_id]
