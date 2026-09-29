-- Prove2me | solution 1 for FiniteTriangular.sum_range_159
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:13.714285+00:00
-- url     : https://prove2.me/submissions/764470a1-7ab9-4dbf-a035-6f3a0f7cba2f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 159, k = 12561 := by
  rw [sum_range_id]
