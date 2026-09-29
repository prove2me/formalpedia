-- Prove2me | solution 1 for FiniteTriangular.sum_range_1062
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:03.960187+00:00
-- url     : https://prove2.me/submissions/d3185c91-34dd-4566-a31a-cab96e64bbe7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1062, k = 563391 := by
  rw [sum_range_id]
