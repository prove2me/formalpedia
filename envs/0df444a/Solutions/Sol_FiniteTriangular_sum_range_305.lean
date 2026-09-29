-- Prove2me | solution 1 for FiniteTriangular.sum_range_305
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:04.212085+00:00
-- url     : https://prove2.me/submissions/117c0fec-1539-4631-b96a-0da709f43650

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 305, k = 46360 := by
  rw [sum_range_id]
