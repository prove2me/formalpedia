-- Prove2me | solution 1 for FiniteTriangular.sum_range_321
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:29.289351+00:00
-- url     : https://prove2.me/submissions/3fe29dfd-87a6-4fff-9937-518268b7a2d2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 321, k = 51360 := by
  rw [sum_range_id]
