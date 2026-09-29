-- Prove2me | solution 1 for FiniteTriangular.sum_range_828
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:43.065537+00:00
-- url     : https://prove2.me/submissions/2f13f616-91ee-40cd-a9e4-d1e9a8279c69

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 828, k = 342378 := by
  rw [sum_range_id]
