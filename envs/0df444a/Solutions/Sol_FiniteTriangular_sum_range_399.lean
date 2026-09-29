-- Prove2me | solution 1 for FiniteTriangular.sum_range_399
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:55.925321+00:00
-- url     : https://prove2.me/submissions/b99c9567-6d3b-45b9-92f2-57f7cdd2b68e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 399, k = 79401 := by
  rw [sum_range_id]
