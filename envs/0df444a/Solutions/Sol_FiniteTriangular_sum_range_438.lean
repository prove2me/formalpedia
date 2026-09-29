-- Prove2me | solution 1 for FiniteTriangular.sum_range_438
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:37.317079+00:00
-- url     : https://prove2.me/submissions/7329a106-33eb-4899-bdaa-e79848b756d5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 438, k = 95703 := by
  rw [sum_range_id]
