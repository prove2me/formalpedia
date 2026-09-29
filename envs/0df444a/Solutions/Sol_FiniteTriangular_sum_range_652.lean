-- Prove2me | solution 1 for FiniteTriangular.sum_range_652
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:02.941628+00:00
-- url     : https://prove2.me/submissions/5c616981-58d9-4779-8e40-1781fa14f44f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 652, k = 212226 := by
  rw [sum_range_id]
