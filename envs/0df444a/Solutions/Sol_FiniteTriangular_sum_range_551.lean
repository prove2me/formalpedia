-- Prove2me | solution 1 for FiniteTriangular.sum_range_551
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:59.412746+00:00
-- url     : https://prove2.me/submissions/e15abf59-b256-448b-a2e8-1daaf836430a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 551, k = 151525 := by
  rw [sum_range_id]
