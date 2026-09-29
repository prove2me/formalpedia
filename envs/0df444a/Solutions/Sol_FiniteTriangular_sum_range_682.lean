-- Prove2me | solution 1 for FiniteTriangular.sum_range_682
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:00.334957+00:00
-- url     : https://prove2.me/submissions/6acee802-cc5f-4c5b-af21-97433f60014b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 682, k = 232221 := by
  rw [sum_range_id]
