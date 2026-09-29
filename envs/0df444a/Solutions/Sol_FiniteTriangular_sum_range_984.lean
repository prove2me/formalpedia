-- Prove2me | solution 1 for FiniteTriangular.sum_range_984
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:14.399421+00:00
-- url     : https://prove2.me/submissions/6a0c94b5-b29d-4a81-a2aa-d3d68ec957d0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 984, k = 483636 := by
  rw [sum_range_id]
