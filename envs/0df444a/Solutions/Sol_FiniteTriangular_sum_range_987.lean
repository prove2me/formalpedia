-- Prove2me | solution 1 for FiniteTriangular.sum_range_987
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:04.953017+00:00
-- url     : https://prove2.me/submissions/aca4f93f-633a-4f1f-a310-90da03aee085

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 987, k = 486591 := by
  rw [sum_range_id]
