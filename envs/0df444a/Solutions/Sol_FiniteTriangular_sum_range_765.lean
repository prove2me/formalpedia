-- Prove2me | solution 1 for FiniteTriangular.sum_range_765
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:51.29549+00:00
-- url     : https://prove2.me/submissions/af73d0b1-238f-4aef-b3cc-d6d0dc5da68d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 765, k = 292230 := by
  rw [sum_range_id]
