-- Prove2me | solution 1 for FiniteTriangular.sum_range_222
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:28.457889+00:00
-- url     : https://prove2.me/submissions/ce4f69f8-4ab7-4f74-a26a-59c0491f2cd7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 222, k = 24531 := by
  rw [sum_range_id]
