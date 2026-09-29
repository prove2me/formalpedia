-- Prove2me | solution 1 for FiniteTriangular.sum_range_669
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:25.120962+00:00
-- url     : https://prove2.me/submissions/aef2b52a-c9d0-4842-a0f5-a548618a95a9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 669, k = 223446 := by
  rw [sum_range_id]
