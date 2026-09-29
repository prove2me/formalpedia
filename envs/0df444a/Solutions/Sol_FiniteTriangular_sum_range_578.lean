-- Prove2me | solution 1 for FiniteTriangular.sum_range_578
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:47.605381+00:00
-- url     : https://prove2.me/submissions/30d35986-3edf-42e7-862f-cb0ba0089da7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 578, k = 166753 := by
  rw [sum_range_id]
