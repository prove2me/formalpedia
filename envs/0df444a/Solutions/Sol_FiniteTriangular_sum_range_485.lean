-- Prove2me | solution 1 for FiniteTriangular.sum_range_485
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:23.061356+00:00
-- url     : https://prove2.me/submissions/e1ca62e7-baf6-48e5-a685-578a8d31fd5b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 485, k = 117370 := by
  rw [sum_range_id]
