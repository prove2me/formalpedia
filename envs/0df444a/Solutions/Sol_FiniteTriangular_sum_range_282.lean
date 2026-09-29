-- Prove2me | solution 1 for FiniteTriangular.sum_range_282
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:41.15352+00:00
-- url     : https://prove2.me/submissions/d07274b5-6f86-4457-8ec6-605b3b01373f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 282, k = 39621 := by
  rw [sum_range_id]
