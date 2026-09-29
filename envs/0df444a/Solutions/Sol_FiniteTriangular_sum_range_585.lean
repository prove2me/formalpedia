-- Prove2me | solution 1 for FiniteTriangular.sum_range_585
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:32.342982+00:00
-- url     : https://prove2.me/submissions/fc05c3ec-ecb6-4c94-be56-4689c38c1b50

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 585, k = 170820 := by
  rw [sum_range_id]
