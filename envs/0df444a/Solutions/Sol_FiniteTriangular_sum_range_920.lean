-- Prove2me | solution 1 for FiniteTriangular.sum_range_920
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:52:02.435038+00:00
-- url     : https://prove2.me/submissions/457073d6-1b60-4679-81e9-5e88804e5b7f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 920, k = 422740 := by
  rw [sum_range_id]
