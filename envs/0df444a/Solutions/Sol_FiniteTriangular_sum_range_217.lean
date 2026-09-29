-- Prove2me | solution 1 for FiniteTriangular.sum_range_217
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:25.498067+00:00
-- url     : https://prove2.me/submissions/06582b32-5adf-497d-83e3-faa4b0bcb7f5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 217, k = 23436 := by
  rw [sum_range_id]
