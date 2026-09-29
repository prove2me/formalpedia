-- Prove2me | solution 1 for FiniteTriangular.sum_range_659
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:48.08865+00:00
-- url     : https://prove2.me/submissions/e84aa1ed-86cd-40c1-b56f-5eab01dce4aa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 659, k = 216811 := by
  rw [sum_range_id]
