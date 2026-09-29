-- Prove2me | solution 1 for FiniteTriangular.sum_range_867
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:41:58.32773+00:00
-- url     : https://prove2.me/submissions/f43b37ad-9b6f-4cf3-882a-aeb9c61219d6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 867, k = 375411 := by
  rw [sum_range_id]
