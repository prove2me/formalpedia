-- Prove2me | solution 1 for FiniteTriangular.sum_range_419
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:03.657075+00:00
-- url     : https://prove2.me/submissions/dacbba5e-2a58-46f2-a2ab-015af3bcd27b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 419, k = 87571 := by
  rw [sum_range_id]
