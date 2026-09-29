-- Prove2me | solution 1 for FiniteTriangular.sum_range_549
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:57.995665+00:00
-- url     : https://prove2.me/submissions/8531f0c2-ea28-4c70-8907-43136e08c938

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 549, k = 150426 := by
  rw [sum_range_id]
