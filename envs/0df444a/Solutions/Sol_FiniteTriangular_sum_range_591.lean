-- Prove2me | solution 1 for FiniteTriangular.sum_range_591
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:36.221454+00:00
-- url     : https://prove2.me/submissions/6506eed7-37af-4d84-b240-d451f4a0b60a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 591, k = 174345 := by
  rw [sum_range_id]
