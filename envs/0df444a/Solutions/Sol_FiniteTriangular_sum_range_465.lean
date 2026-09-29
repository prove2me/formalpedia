-- Prove2me | solution 1 for FiniteTriangular.sum_range_465
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:48.810766+00:00
-- url     : https://prove2.me/submissions/66404c23-05c6-4c1b-b64a-49e189bc9a90

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 465, k = 107880 := by
  rw [sum_range_id]
