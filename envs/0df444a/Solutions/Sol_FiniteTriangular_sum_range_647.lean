-- Prove2me | solution 1 for FiniteTriangular.sum_range_647
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:27.506372+00:00
-- url     : https://prove2.me/submissions/1118c111-4175-468a-8fa4-08e3f470cf8b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 647, k = 208981 := by
  rw [sum_range_id]
