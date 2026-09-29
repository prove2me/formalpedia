-- Prove2me | solution 1 for FiniteTriangular.sum_range_796
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:45.014443+00:00
-- url     : https://prove2.me/submissions/9cf387f2-90dc-4c45-88f7-795e76bbd789

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 796, k = 316410 := by
  rw [sum_range_id]
