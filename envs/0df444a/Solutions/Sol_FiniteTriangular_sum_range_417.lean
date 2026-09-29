-- Prove2me | solution 1 for FiniteTriangular.sum_range_417
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:02.133266+00:00
-- url     : https://prove2.me/submissions/7ea18e21-7861-438a-9727-a9e707e938eb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 417, k = 86736 := by
  rw [sum_range_id]
