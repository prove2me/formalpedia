-- Prove2me | solution 1 for FiniteTriangular.sum_range_1059
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:01.500497+00:00
-- url     : https://prove2.me/submissions/79dfea10-246c-414e-9a1e-cce60eae85dd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1059, k = 560211 := by
  rw [sum_range_id]
