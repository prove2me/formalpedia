-- Prove2me | solution 1 for FiniteTriangular.sum_range_386
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:06.687848+00:00
-- url     : https://prove2.me/submissions/23f2edae-b009-4a1c-a3f2-dba8f2fe69ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 386, k = 74305 := by
  rw [sum_range_id]
