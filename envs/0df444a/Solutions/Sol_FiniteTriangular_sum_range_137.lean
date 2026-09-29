-- Prove2me | solution 1 for FiniteTriangular.sum_range_137
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:49.117111+00:00
-- url     : https://prove2.me/submissions/8b88b964-247c-4c95-b933-b8983299b236

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 137, k = 9316 := by
  rw [sum_range_id]
