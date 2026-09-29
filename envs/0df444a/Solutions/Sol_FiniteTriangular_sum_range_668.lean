-- Prove2me | solution 1 for FiniteTriangular.sum_range_668
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:24.524777+00:00
-- url     : https://prove2.me/submissions/461c5239-efbb-4e85-bd6b-304b68a7e7a0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 668, k = 222778 := by
  rw [sum_range_id]
