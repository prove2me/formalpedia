-- Prove2me | solution 1 for FiniteTriangular.sum_range_360
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:30.745368+00:00
-- url     : https://prove2.me/submissions/1fa566a1-7043-4a45-ae59-e588a06c7359

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 360, k = 64620 := by
  rw [sum_range_id]
