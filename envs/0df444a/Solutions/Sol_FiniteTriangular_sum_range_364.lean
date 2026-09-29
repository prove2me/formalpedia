-- Prove2me | solution 1 for FiniteTriangular.sum_range_364
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:23.232604+00:00
-- url     : https://prove2.me/submissions/16078aa6-bc84-4a9b-bc66-e2af6e55c39d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 364, k = 66066 := by
  rw [sum_range_id]
