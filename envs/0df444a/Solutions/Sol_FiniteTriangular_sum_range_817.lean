-- Prove2me | solution 1 for FiniteTriangular.sum_range_817
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:53.457496+00:00
-- url     : https://prove2.me/submissions/e744e616-c256-4fd3-985f-c19af4b3bbca

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 817, k = 333336 := by
  rw [sum_range_id]
