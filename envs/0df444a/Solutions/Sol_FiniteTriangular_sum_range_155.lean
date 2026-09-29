-- Prove2me | solution 1 for FiniteTriangular.sum_range_155
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:48.050739+00:00
-- url     : https://prove2.me/submissions/15f89436-887c-4f06-a6ce-e0ef4fcf7761

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 155, k = 11935 := by
  rw [sum_range_id]
