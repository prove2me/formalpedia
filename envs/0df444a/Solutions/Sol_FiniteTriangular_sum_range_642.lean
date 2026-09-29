-- Prove2me | solution 1 for FiniteTriangular.sum_range_642
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:24.577017+00:00
-- url     : https://prove2.me/submissions/3b1d7a49-86d2-4e38-a250-3c496c461e99

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 642, k = 205761 := by
  rw [sum_range_id]
