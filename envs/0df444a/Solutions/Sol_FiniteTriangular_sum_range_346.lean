-- Prove2me | solution 1 for FiniteTriangular.sum_range_346
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:49.208541+00:00
-- url     : https://prove2.me/submissions/a405596d-6e8c-4f06-b267-51963a06aff0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 346, k = 59685 := by
  rw [sum_range_id]
