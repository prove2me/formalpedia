-- Prove2me | solution 1 for FiniteTriangular.sum_range_862
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:12.823192+00:00
-- url     : https://prove2.me/submissions/8dfe0c9f-4c56-44f7-8a17-c4f7df403e83

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 862, k = 371091 := by
  rw [sum_range_id]
