-- Prove2me | solution 1 for FiniteTriangular.sum_range_618
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:19.069915+00:00
-- url     : https://prove2.me/submissions/1e78df41-796a-4d67-b84a-5c69f4838457

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 618, k = 190653 := by
  rw [sum_range_id]
