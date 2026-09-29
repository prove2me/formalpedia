-- Prove2me | solution 1 for FiniteTriangular.sum_range_391
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:10.104597+00:00
-- url     : https://prove2.me/submissions/00a2c3e5-9c5f-4d6f-b941-59521f6b23a6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 391, k = 76245 := by
  rw [sum_range_id]
