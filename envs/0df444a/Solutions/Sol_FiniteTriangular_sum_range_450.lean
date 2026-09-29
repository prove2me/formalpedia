-- Prove2me | solution 1 for FiniteTriangular.sum_range_450
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:00.203822+00:00
-- url     : https://prove2.me/submissions/e66d0d67-7d45-4740-9f74-221107be71f3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 450, k = 101025 := by
  rw [sum_range_id]
