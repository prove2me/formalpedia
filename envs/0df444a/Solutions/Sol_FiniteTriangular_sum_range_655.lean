-- Prove2me | solution 1 for FiniteTriangular.sum_range_655
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:05.178668+00:00
-- url     : https://prove2.me/submissions/e6b15ea0-acfe-4cc2-a694-d856baf43f3d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 655, k = 214185 := by
  rw [sum_range_id]
