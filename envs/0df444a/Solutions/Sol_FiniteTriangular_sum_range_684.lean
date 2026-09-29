-- Prove2me | solution 1 for FiniteTriangular.sum_range_684
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:01.58224+00:00
-- url     : https://prove2.me/submissions/ddfeec10-070d-42e4-936d-0d8f5c62b0ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 684, k = 233586 := by
  rw [sum_range_id]
