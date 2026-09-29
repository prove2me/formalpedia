-- Prove2me | solution 1 for FiniteTriangular.sum_range_1110
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:33.678688+00:00
-- url     : https://prove2.me/submissions/326747a8-c2b7-4f2e-86cf-5e7fd6c7fd43

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1110, k = 615495 := by
  rw [sum_range_id]
