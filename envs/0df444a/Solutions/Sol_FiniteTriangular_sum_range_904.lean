-- Prove2me | solution 1 for FiniteTriangular.sum_range_904
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:47.559272+00:00
-- url     : https://prove2.me/submissions/c68c176f-b936-482e-b2b6-d2e4550c663f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 904, k = 408156 := by
  rw [sum_range_id]
