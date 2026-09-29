-- Prove2me | solution 1 for FiniteTriangular.sum_range_1030
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:57.457988+00:00
-- url     : https://prove2.me/submissions/a0ae8142-6e32-4591-9df6-42cab41d2a60

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1030, k = 529935 := by
  rw [sum_range_id]
