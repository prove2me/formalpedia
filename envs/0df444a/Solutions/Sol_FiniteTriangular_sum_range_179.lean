-- Prove2me | solution 1 for FiniteTriangular.sum_range_179
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:21.987551+00:00
-- url     : https://prove2.me/submissions/031a8bc5-5f19-44d7-a730-0f728fdcdce0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 179, k = 15931 := by
  rw [sum_range_id]
