-- Prove2me | solution 1 for FiniteTriangular.sum_range_243
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:24.636973+00:00
-- url     : https://prove2.me/submissions/0dbb4ff4-3f9b-4c38-bf61-68f0082e0be1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 243, k = 29403 := by
  rw [sum_range_id]
