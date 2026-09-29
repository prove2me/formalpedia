-- Prove2me | solution 1 for FiniteTriangular.sum_range_745
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:30.470651+00:00
-- url     : https://prove2.me/submissions/4e322e77-4d7b-499a-8c25-787c1b339018

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 745, k = 277140 := by
  rw [sum_range_id]
