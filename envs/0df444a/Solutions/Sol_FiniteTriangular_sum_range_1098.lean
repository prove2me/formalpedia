-- Prove2me | solution 1 for FiniteTriangular.sum_range_1098
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:40.975981+00:00
-- url     : https://prove2.me/submissions/234ce739-03ef-4844-a6be-0d6143954588

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1098, k = 602253 := by
  rw [sum_range_id]
