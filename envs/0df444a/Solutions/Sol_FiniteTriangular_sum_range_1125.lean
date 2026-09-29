-- Prove2me | solution 1 for FiniteTriangular.sum_range_1125
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:43.554664+00:00
-- url     : https://prove2.me/submissions/67272b59-f6b8-477d-bf7d-d846758fb149

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1125, k = 632250 := by
  rw [sum_range_id]
