-- Prove2me | solution 1 for FiniteTriangular.sum_range_1027
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:55.420775+00:00
-- url     : https://prove2.me/submissions/a9644a1c-ed47-4c7a-bb1f-a4fc971cb21c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1027, k = 526851 := by
  rw [sum_range_id]
