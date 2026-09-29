-- Prove2me | solution 1 for FiniteTriangular.sum_range_1122
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:41.306711+00:00
-- url     : https://prove2.me/submissions/118f2d89-04af-449f-991f-1d268c5da1ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1122, k = 628881 := by
  rw [sum_range_id]
