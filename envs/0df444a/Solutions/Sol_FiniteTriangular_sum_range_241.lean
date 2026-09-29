-- Prove2me | solution 1 for FiniteTriangular.sum_range_241
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:23.323099+00:00
-- url     : https://prove2.me/submissions/8419a888-d934-4b65-9f04-e6d733ff0f80

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 241, k = 28920 := by
  rw [sum_range_id]
