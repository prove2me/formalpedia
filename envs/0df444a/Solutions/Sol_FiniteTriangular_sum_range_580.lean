-- Prove2me | solution 1 for FiniteTriangular.sum_range_580
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:48.812988+00:00
-- url     : https://prove2.me/submissions/8d893734-0c85-410f-92a1-51594debcabe

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 580, k = 167910 := by
  rw [sum_range_id]
