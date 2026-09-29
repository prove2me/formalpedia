-- Prove2me | solution 1 for FiniteTriangular.sum_range_771
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:38.035917+00:00
-- url     : https://prove2.me/submissions/0b3511aa-1c69-4689-8738-6b1ff4dd02d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 771, k = 296835 := by
  rw [sum_range_id]
