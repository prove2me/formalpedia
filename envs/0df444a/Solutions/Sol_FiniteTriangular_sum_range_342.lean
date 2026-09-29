-- Prove2me | solution 1 for FiniteTriangular.sum_range_342
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:06.822935+00:00
-- url     : https://prove2.me/submissions/ca70c3a8-471a-4013-8988-36c6735b6c50

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 342, k = 58311 := by
  rw [sum_range_id]
