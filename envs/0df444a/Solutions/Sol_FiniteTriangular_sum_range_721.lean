-- Prove2me | solution 1 for FiniteTriangular.sum_range_721
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:10:57.211652+00:00
-- url     : https://prove2.me/submissions/76660cf9-9457-448b-88a1-1f6535ffef5a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 721, k = 259560 := by
  rw [sum_range_id]
