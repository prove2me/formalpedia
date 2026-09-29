-- Prove2me | solution 1 for FiniteTriangular.sum_range_307
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:05.679058+00:00
-- url     : https://prove2.me/submissions/af109350-9e67-40d5-9fe4-2d786a303600

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 307, k = 46971 := by
  rw [sum_range_id]
