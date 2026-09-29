-- Prove2me | solution 1 for FiniteTriangular.sum_range_809
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:05.173534+00:00
-- url     : https://prove2.me/submissions/f7ee26c9-2258-42d4-8ea6-e2da77e4eade

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 809, k = 326836 := by
  rw [sum_range_id]
