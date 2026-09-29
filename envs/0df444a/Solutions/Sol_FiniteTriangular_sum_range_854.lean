-- Prove2me | solution 1 for FiniteTriangular.sum_range_854
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:34.394205+00:00
-- url     : https://prove2.me/submissions/e4b56074-4132-45a5-a5e8-f2a535d84704

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 854, k = 364231 := by
  rw [sum_range_id]
