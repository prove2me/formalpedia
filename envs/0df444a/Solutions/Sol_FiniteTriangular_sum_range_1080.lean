-- Prove2me | solution 1 for FiniteTriangular.sum_range_1080
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:34.693187+00:00
-- url     : https://prove2.me/submissions/7850b8d9-4d95-4e9c-8f86-3246958ec758

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1080, k = 582660 := by
  rw [sum_range_id]
