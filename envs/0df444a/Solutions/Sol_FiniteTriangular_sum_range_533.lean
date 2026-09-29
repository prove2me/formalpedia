-- Prove2me | solution 1 for FiniteTriangular.sum_range_533
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:30.679092+00:00
-- url     : https://prove2.me/submissions/f4daa4d5-ebea-497c-a7ea-bb61b886da35

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 533, k = 141778 := by
  rw [sum_range_id]
