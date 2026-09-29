-- Prove2me | solution 1 for FiniteTriangular.sum_range_1120
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:09.761606+00:00
-- url     : https://prove2.me/submissions/3f9eac66-25b1-4a83-8047-571f507b8afd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1120, k = 626640 := by
  rw [sum_range_id]
