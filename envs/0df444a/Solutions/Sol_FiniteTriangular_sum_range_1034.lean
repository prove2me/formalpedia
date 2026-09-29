-- Prove2me | solution 1 for FiniteTriangular.sum_range_1034
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:55.21802+00:00
-- url     : https://prove2.me/submissions/693551cd-332d-40b4-a798-466f4878d20f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1034, k = 534061 := by
  rw [sum_range_id]
