-- Prove2me | solution 1 for FiniteTriangular.sum_range_463
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:05.969024+00:00
-- url     : https://prove2.me/submissions/16943558-8b25-44d8-83cd-d3c58e922871

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 463, k = 106953 := by
  rw [sum_range_id]
