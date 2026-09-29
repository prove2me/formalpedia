-- Prove2me | solution 1 for FiniteTriangular.sum_range_973
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:26.222908+00:00
-- url     : https://prove2.me/submissions/984027ab-5abc-4346-852a-5d7c8a7e9118

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 973, k = 472878 := by
  rw [sum_range_id]
