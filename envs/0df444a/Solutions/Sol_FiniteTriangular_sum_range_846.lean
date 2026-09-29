-- Prove2me | solution 1 for FiniteTriangular.sum_range_846
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:58.45464+00:00
-- url     : https://prove2.me/submissions/bfe194d8-b9d2-4bd3-9b24-f1bff6ec4a3a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 846, k = 357435 := by
  rw [sum_range_id]
