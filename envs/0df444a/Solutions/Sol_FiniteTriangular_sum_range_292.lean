-- Prove2me | solution 1 for FiniteTriangular.sum_range_292
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:19.280608+00:00
-- url     : https://prove2.me/submissions/ad034826-29c8-4b10-9115-1e1d5969a25d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 292, k = 42486 := by
  rw [sum_range_id]
