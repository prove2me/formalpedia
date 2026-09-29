-- Prove2me | solution 1 for FiniteTriangular.sum_range_943
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:13.747538+00:00
-- url     : https://prove2.me/submissions/e4fe5b5d-ea37-4b7f-8363-1cea0d97cde6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 943, k = 444153 := by
  rw [sum_range_id]
