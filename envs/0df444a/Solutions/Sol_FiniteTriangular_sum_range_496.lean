-- Prove2me | solution 1 for FiniteTriangular.sum_range_496
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:19:01.304845+00:00
-- url     : https://prove2.me/submissions/ebd85843-dc49-44a7-b9f3-9d6de4bc03e2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 496, k = 122760 := by
  rw [sum_range_id]
