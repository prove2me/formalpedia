-- Prove2me | solution 1 for FiniteTriangular.sum_range_528
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:55.060554+00:00
-- url     : https://prove2.me/submissions/34042a63-db11-49fa-b90d-b1a2359f62e7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 528, k = 139128 := by
  rw [sum_range_id]
