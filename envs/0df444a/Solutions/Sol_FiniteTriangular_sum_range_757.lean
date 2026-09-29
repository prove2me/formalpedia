-- Prove2me | solution 1 for FiniteTriangular.sum_range_757
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:13.586016+00:00
-- url     : https://prove2.me/submissions/f24117aa-cdd9-4ac8-9d40-9bd3c08a40f7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 757, k = 286146 := by
  rw [sum_range_id]
