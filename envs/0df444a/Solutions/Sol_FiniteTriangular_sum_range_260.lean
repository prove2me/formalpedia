-- Prove2me | solution 1 for FiniteTriangular.sum_range_260
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:14.837541+00:00
-- url     : https://prove2.me/submissions/4018c1b7-65b8-4891-af47-7ac30b295d0b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 260, k = 33670 := by
  rw [sum_range_id]
