-- Prove2me | solution 1 for FiniteTriangular.sum_range_437
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:36.736504+00:00
-- url     : https://prove2.me/submissions/2b23919c-25e7-4823-8564-621117f270d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 437, k = 95266 := by
  rw [sum_range_id]
