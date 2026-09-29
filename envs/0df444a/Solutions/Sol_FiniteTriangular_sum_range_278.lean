-- Prove2me | solution 1 for FiniteTriangular.sum_range_278
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:55.489982+00:00
-- url     : https://prove2.me/submissions/9cb5c74b-2a32-4ebb-9a84-8bbae2bc91ee

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 278, k = 38503 := by
  rw [sum_range_id]
