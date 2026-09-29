-- Prove2me | solution 1 for FiniteTriangular.sum_range_474
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:36.466167+00:00
-- url     : https://prove2.me/submissions/1019b05e-d9c6-43f6-a089-be52a27dda53

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 474, k = 112101 := by
  rw [sum_range_id]
