-- Prove2me | solution 1 for FiniteTriangular.sum_range_772
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:38.618863+00:00
-- url     : https://prove2.me/submissions/579f8a90-2d5f-4bea-8049-1097110e8b31

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 772, k = 297606 := by
  rw [sum_range_id]
