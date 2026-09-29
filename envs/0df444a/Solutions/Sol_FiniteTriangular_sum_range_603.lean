-- Prove2me | solution 1 for FiniteTriangular.sum_range_603
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:54.466979+00:00
-- url     : https://prove2.me/submissions/3027ba82-3531-4632-a5fe-b19d9dfcd2a7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 603, k = 181503 := by
  rw [sum_range_id]
