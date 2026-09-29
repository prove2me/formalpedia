-- Prove2me | solution 1 for FiniteTriangular.sum_range_138
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:49.703156+00:00
-- url     : https://prove2.me/submissions/f1d135d5-96b9-4f7c-9cbb-2dc0be6e682c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 138, k = 9453 := by
  rw [sum_range_id]
