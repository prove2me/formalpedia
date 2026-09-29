-- Prove2me | solution 1 for FiniteTriangular.sum_range_814
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:08.545106+00:00
-- url     : https://prove2.me/submissions/04d3019c-3a2a-4ebc-8e16-9df3f17fcc5f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 814, k = 330891 := by
  rw [sum_range_id]
