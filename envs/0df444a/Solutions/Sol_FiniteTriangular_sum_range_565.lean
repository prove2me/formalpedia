-- Prove2me | solution 1 for FiniteTriangular.sum_range_565
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:19.638355+00:00
-- url     : https://prove2.me/submissions/261842c7-6b5d-4d9d-b570-e708aa07083d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 565, k = 159330 := by
  rw [sum_range_id]
