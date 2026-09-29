-- Prove2me | solution 1 for FiniteTriangular.sum_range_964
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:47.696906+00:00
-- url     : https://prove2.me/submissions/97f94616-d31b-4bf3-8978-c6d16b55f144

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 964, k = 464166 := by
  rw [sum_range_id]
