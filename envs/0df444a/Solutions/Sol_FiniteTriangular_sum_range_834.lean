-- Prove2me | solution 1 for FiniteTriangular.sum_range_834
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:20.037187+00:00
-- url     : https://prove2.me/submissions/d8ac6ad0-8b9c-43b3-b5d6-e9ea7858117d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 834, k = 347361 := by
  rw [sum_range_id]
