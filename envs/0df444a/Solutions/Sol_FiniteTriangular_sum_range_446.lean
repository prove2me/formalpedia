-- Prove2me | solution 1 for FiniteTriangular.sum_range_446
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:16.356987+00:00
-- url     : https://prove2.me/submissions/abcd7e7f-fe08-4b31-b25a-0b0431644e97

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 446, k = 99235 := by
  rw [sum_range_id]
