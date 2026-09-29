-- Prove2me | solution 1 for FiniteTriangular.sum_range_274
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:53.029982+00:00
-- url     : https://prove2.me/submissions/80068962-7dc9-42cd-a749-a30a691cc7f1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 274, k = 37401 := by
  rw [sum_range_id]
