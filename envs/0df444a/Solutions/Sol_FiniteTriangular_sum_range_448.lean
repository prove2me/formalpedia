-- Prove2me | solution 1 for FiniteTriangular.sum_range_448
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:17.558265+00:00
-- url     : https://prove2.me/submissions/969b5024-72bc-4aa9-b9d0-2a3f9d41192e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 448, k = 100128 := by
  rw [sum_range_id]
