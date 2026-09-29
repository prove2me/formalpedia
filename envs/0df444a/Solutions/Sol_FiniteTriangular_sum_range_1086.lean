-- Prove2me | solution 1 for FiniteTriangular.sum_range_1086
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:28.707116+00:00
-- url     : https://prove2.me/submissions/852a8e65-3dd1-4906-8bff-b8efd0cb47e8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1086, k = 589155 := by
  rw [sum_range_id]
