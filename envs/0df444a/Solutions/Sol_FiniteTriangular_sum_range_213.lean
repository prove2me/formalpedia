-- Prove2me | solution 1 for FiniteTriangular.sum_range_213
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:43.585495+00:00
-- url     : https://prove2.me/submissions/09a5788b-107a-4e9a-a343-5ae4bcaa67b7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 213, k = 22578 := by
  rw [sum_range_id]
