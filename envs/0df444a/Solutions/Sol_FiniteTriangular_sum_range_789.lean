-- Prove2me | solution 1 for FiniteTriangular.sum_range_789
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:08.058353+00:00
-- url     : https://prove2.me/submissions/64f8775b-071a-452b-b378-2c05fbc4b466

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 789, k = 310866 := by
  rw [sum_range_id]
