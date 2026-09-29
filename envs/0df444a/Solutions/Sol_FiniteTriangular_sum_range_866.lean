-- Prove2me | solution 1 for FiniteTriangular.sum_range_866
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:41:57.673003+00:00
-- url     : https://prove2.me/submissions/3d4457d5-d372-416b-94be-2944a8391c74

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 866, k = 374545 := by
  rw [sum_range_id]
