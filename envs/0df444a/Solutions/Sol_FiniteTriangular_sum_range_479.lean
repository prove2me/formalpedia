-- Prove2me | solution 1 for FiniteTriangular.sum_range_479
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:39.489652+00:00
-- url     : https://prove2.me/submissions/9e61c6d4-d6e4-4149-81d2-b0a823fa7c41

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 479, k = 114481 := by
  rw [sum_range_id]
