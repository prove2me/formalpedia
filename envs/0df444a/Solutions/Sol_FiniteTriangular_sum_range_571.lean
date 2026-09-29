-- Prove2me | solution 1 for FiniteTriangular.sum_range_571
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:03.805636+00:00
-- url     : https://prove2.me/submissions/72c00cc8-3913-4c1c-b1e4-e57b4ee09943

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 571, k = 162735 := by
  rw [sum_range_id]
