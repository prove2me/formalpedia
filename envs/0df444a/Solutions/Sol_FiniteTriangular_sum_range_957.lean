-- Prove2me | solution 1 for FiniteTriangular.sum_range_957
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:01:01.28747+00:00
-- url     : https://prove2.me/submissions/4defdd36-7f38-4c2b-b617-4e04f2d3c79e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 957, k = 457446 := by
  rw [sum_range_id]
