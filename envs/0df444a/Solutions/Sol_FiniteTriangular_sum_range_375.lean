-- Prove2me | solution 1 for FiniteTriangular.sum_range_375
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:18.627604+00:00
-- url     : https://prove2.me/submissions/5698aec0-277d-4620-925c-6df2174b7781

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 375, k = 70125 := by
  rw [sum_range_id]
