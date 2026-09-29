-- Prove2me | solution 1 for FiniteTriangular.sum_range_535
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:31.993444+00:00
-- url     : https://prove2.me/submissions/fd68c24d-6c28-474f-9600-8e8474bb90e3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 535, k = 142845 := by
  rw [sum_range_id]
