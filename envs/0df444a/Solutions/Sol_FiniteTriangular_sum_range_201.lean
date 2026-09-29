-- Prove2me | solution 1 for FiniteTriangular.sum_range_201
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:26.79236+00:00
-- url     : https://prove2.me/submissions/53cbb4d2-44a5-4e68-b84c-fb6491a9ee33

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 201, k = 20100 := by
  rw [sum_range_id]
