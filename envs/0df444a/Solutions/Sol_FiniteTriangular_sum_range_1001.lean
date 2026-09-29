-- Prove2me | solution 1 for FiniteTriangular.sum_range_1001
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:48.809586+00:00
-- url     : https://prove2.me/submissions/a1ea7845-29d4-4ee8-a531-b565240092ee

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1001, k = 500500 := by
  rw [sum_range_id]
