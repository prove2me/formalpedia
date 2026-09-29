-- Prove2me | solution 1 for FiniteTriangular.sum_range_411
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:17.531197+00:00
-- url     : https://prove2.me/submissions/caaebd43-239f-450a-8e8e-545090e7f389

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 411, k = 84255 := by
  rw [sum_range_id]
