-- Prove2me | solution 1 for FiniteTriangular.sum_range_873
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:40.490439+00:00
-- url     : https://prove2.me/submissions/8c936969-d426-450c-bca4-8560ad6719b0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 873, k = 380628 := by
  rw [sum_range_id]
