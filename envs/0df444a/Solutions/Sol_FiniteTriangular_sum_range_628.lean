-- Prove2me | solution 1 for FiniteTriangular.sum_range_628
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:04.837221+00:00
-- url     : https://prove2.me/submissions/616b9d07-5bec-45c4-b91e-31d804b4b603

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 628, k = 196878 := by
  rw [sum_range_id]
