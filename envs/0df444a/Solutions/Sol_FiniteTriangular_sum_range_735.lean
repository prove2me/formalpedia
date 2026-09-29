-- Prove2me | solution 1 for FiniteTriangular.sum_range_735
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:47.467454+00:00
-- url     : https://prove2.me/submissions/97660abe-7dd2-428f-ad8f-1cbb1a5fa028

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 735, k = 269745 := by
  rw [sum_range_id]
