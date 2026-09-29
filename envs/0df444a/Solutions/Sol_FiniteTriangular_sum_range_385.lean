-- Prove2me | solution 1 for FiniteTriangular.sum_range_385
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:06.065658+00:00
-- url     : https://prove2.me/submissions/8d9420db-073b-4528-8b20-36221737b5db

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 385, k = 73920 := by
  rw [sum_range_id]
