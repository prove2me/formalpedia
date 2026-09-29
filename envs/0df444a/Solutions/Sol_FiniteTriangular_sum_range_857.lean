-- Prove2me | solution 1 for FiniteTriangular.sum_range_857
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:09.353094+00:00
-- url     : https://prove2.me/submissions/4cbcaf8d-6356-4e91-ad84-76f33e4fbc3d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 857, k = 366796 := by
  rw [sum_range_id]
