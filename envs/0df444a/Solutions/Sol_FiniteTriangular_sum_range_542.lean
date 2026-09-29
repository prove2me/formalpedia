-- Prove2me | solution 1 for FiniteTriangular.sum_range_542
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:08.351365+00:00
-- url     : https://prove2.me/submissions/48d73294-cab7-42d2-8f57-e0792664b1d1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 542, k = 146611 := by
  rw [sum_range_id]
