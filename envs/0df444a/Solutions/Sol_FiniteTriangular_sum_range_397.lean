-- Prove2me | solution 1 for FiniteTriangular.sum_range_397
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:54.842202+00:00
-- url     : https://prove2.me/submissions/6ea25886-9d43-4a33-90d0-06d6fbc48ed0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 397, k = 78606 := by
  rw [sum_range_id]
