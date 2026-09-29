-- Prove2me | solution 1 for FiniteTriangular.sum_range_402
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:31.256902+00:00
-- url     : https://prove2.me/submissions/4503334e-f96b-4db6-b150-d4faf259048c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 402, k = 80601 := by
  rw [sum_range_id]
