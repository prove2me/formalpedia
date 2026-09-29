-- Prove2me | solution 1 for FiniteTriangular.sum_range_727
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:11:01.164656+00:00
-- url     : https://prove2.me/submissions/851f6e07-6a02-4507-b96e-dc2f8c86301d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 727, k = 263901 := by
  rw [sum_range_id]
