-- Prove2me | solution 1 for FiniteTriangular.sum_range_548
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:57.180183+00:00
-- url     : https://prove2.me/submissions/5e5ab900-8b0b-4038-9547-9b1d8c943b39

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 548, k = 149878 := by
  rw [sum_range_id]
