-- Prove2me | solution 1 for FiniteTriangular.sum_range_341
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:06.237614+00:00
-- url     : https://prove2.me/submissions/5cec8048-d672-4ab1-8d43-e09540a99a72

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 341, k = 57970 := by
  rw [sum_range_id]
