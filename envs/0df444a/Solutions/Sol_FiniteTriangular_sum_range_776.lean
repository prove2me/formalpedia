-- Prove2me | solution 1 for FiniteTriangular.sum_range_776
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:40.98378+00:00
-- url     : https://prove2.me/submissions/21212cd4-5cff-4838-9b3c-759bb3989667

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 776, k = 300700 := by
  rw [sum_range_id]
