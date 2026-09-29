-- Prove2me | solution 1 for FiniteTriangular.sum_range_284
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:42.38712+00:00
-- url     : https://prove2.me/submissions/292bab7f-3fdb-48fa-8c87-fd6ab21d0677

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 284, k = 40186 := by
  rw [sum_range_id]
