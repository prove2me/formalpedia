-- Prove2me | solution 1 for FiniteTriangular.sum_range_267
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:12:59.533314+00:00
-- url     : https://prove2.me/submissions/df742487-ea88-48e5-9791-dbb403045511

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 267, k = 35511 := by
  rw [sum_range_id]
