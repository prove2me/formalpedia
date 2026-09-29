-- Prove2me | solution 1 for FiniteTriangular.sum_range_351
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:52.971881+00:00
-- url     : https://prove2.me/submissions/e5d95cf0-ce5a-4223-a112-1d1f7bf513af

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 351, k = 61425 := by
  rw [sum_range_id]
