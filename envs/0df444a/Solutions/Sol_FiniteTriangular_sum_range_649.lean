-- Prove2me | solution 1 for FiniteTriangular.sum_range_649
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:00.966972+00:00
-- url     : https://prove2.me/submissions/1419cf85-78ce-4dbf-9c05-d617a931fb6a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 649, k = 210276 := by
  rw [sum_range_id]
