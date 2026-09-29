-- Prove2me | solution 1 for FiniteTriangular.sum_range_1101
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:42.838117+00:00
-- url     : https://prove2.me/submissions/d1617722-1cea-479f-9daa-56a899bb97da

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1101, k = 605550 := by
  rw [sum_range_id]
