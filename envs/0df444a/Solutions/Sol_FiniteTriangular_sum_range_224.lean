-- Prove2me | solution 1 for FiniteTriangular.sum_range_224
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:29.846845+00:00
-- url     : https://prove2.me/submissions/56e6cd3f-b75b-4f83-839a-55c7edf2db3d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 224, k = 24976 := by
  rw [sum_range_id]
