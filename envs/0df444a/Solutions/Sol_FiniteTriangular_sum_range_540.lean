-- Prove2me | solution 1 for FiniteTriangular.sum_range_540
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:07.209295+00:00
-- url     : https://prove2.me/submissions/6c68340e-1a56-4480-a56e-d0c5f03f01d6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 540, k = 145530 := by
  rw [sum_range_id]
