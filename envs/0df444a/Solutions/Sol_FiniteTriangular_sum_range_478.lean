-- Prove2me | solution 1 for FiniteTriangular.sum_range_478
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:38.847916+00:00
-- url     : https://prove2.me/submissions/4610bf25-a3b4-4ab7-919f-793534447c31

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 478, k = 114003 := by
  rw [sum_range_id]
