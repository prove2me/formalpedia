-- Prove2me | solution 1 for FiniteTriangular.sum_range_1068
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:48.573881+00:00
-- url     : https://prove2.me/submissions/6057b630-570d-4e53-93cb-938d0f146be9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1068, k = 569778 := by
  rw [sum_range_id]
