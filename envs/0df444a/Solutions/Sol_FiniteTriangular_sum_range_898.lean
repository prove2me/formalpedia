-- Prove2me | solution 1 for FiniteTriangular.sum_range_898
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:43.385908+00:00
-- url     : https://prove2.me/submissions/e29088f0-8f5d-4403-9d93-584d2e11e915

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 898, k = 402753 := by
  rw [sum_range_id]
