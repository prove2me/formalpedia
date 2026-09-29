-- Prove2me | solution 1 for FiniteTriangular.sum_range_813
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:07.936409+00:00
-- url     : https://prove2.me/submissions/c7582e05-6c55-4eb8-9e2d-4837f299a314

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 813, k = 330078 := by
  rw [sum_range_id]
