-- Prove2me | solution 1 for FiniteTriangular.sum_range_256
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:18.909373+00:00
-- url     : https://prove2.me/submissions/0d45746e-9d03-43e2-a4c9-cd61a1e45012

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 256, k = 32640 := by
  rw [sum_range_id]
