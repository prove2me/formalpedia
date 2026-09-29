-- Prove2me | solution 1 for FiniteTriangular.sum_range_925
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:47.305654+00:00
-- url     : https://prove2.me/submissions/565f9e53-bcf6-45d2-a695-a6d64a24a4c9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 925, k = 427350 := by
  rw [sum_range_id]
