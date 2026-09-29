-- Prove2me | solution 1 for FiniteTriangular.sum_range_517
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:07.437194+00:00
-- url     : https://prove2.me/submissions/ee0c467b-606d-44e7-b227-afc0cbd0e5bf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 517, k = 133386 := by
  rw [sum_range_id]
