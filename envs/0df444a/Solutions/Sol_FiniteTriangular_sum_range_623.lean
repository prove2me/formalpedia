-- Prove2me | solution 1 for FiniteTriangular.sum_range_623
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:22.184682+00:00
-- url     : https://prove2.me/submissions/6c8cc0a6-6584-4893-b711-d69fe795ce00

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 623, k = 193753 := by
  rw [sum_range_id]
