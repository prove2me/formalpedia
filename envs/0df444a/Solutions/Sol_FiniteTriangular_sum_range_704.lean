-- Prove2me | solution 1 for FiniteTriangular.sum_range_704
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:13.901983+00:00
-- url     : https://prove2.me/submissions/805bd621-1e58-4bbb-83f3-83e3845e9e28

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 704, k = 247456 := by
  rw [sum_range_id]
