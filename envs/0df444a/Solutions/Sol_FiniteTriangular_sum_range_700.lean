-- Prove2me | solution 1 for FiniteTriangular.sum_range_700
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:11.470729+00:00
-- url     : https://prove2.me/submissions/d3c6f770-675f-41e2-a954-67b7fa55d0a4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 700, k = 244650 := by
  rw [sum_range_id]
