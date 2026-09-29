-- Prove2me | solution 1 for FiniteTriangular.sum_range_1089
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:23:58.259785+00:00
-- url     : https://prove2.me/submissions/1addc8e4-cb8b-42d5-a0cf-8d77d6e0f6b0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1089, k = 592416 := by
  rw [sum_range_id]
