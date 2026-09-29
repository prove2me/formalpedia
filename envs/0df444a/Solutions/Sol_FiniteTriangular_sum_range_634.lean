-- Prove2me | solution 1 for FiniteTriangular.sum_range_634
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:50.011985+00:00
-- url     : https://prove2.me/submissions/ef6db6d6-aaaf-4d39-9510-1f0a5b9f7f17

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 634, k = 200661 := by
  rw [sum_range_id]
