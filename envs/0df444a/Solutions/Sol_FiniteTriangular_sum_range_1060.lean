-- Prove2me | solution 1 for FiniteTriangular.sum_range_1060
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:02.17958+00:00
-- url     : https://prove2.me/submissions/be686032-eee9-4605-861a-a74ab9c63f76

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1060, k = 561270 := by
  rw [sum_range_id]
