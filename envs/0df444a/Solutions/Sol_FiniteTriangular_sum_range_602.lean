-- Prove2me | solution 1 for FiniteTriangular.sum_range_602
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:53.833132+00:00
-- url     : https://prove2.me/submissions/17a87577-61f5-4369-ad7b-b0bf396658d9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 602, k = 180901 := by
  rw [sum_range_id]
