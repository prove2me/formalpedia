-- Prove2me | solution 1 for FiniteTriangular.sum_range_897
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:42.81018+00:00
-- url     : https://prove2.me/submissions/2e31775a-9519-423b-a736-f2aa51e74502

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 897, k = 401856 := by
  rw [sum_range_id]
