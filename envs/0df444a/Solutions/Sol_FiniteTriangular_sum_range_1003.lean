-- Prove2me | solution 1 for FiniteTriangular.sum_range_1003
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:49.992993+00:00
-- url     : https://prove2.me/submissions/b268f121-78d9-4c16-aca5-95fdcc498d31

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1003, k = 502503 := by
  rw [sum_range_id]
