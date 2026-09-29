-- Prove2me | solution 1 for FiniteTriangular.sum_range_123
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:12:21.91736+00:00
-- url     : https://prove2.me/submissions/5cc6764f-27af-42c4-a6c1-e719e0c1d63c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 123, k = 7503 := by
  rw [sum_range_id]
