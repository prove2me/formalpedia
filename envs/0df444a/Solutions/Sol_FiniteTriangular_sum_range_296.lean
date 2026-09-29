-- Prove2me | solution 1 for FiniteTriangular.sum_range_296
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:21.594686+00:00
-- url     : https://prove2.me/submissions/31a52b67-625a-4a3d-bf82-1f19a81fc942

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 296, k = 43660 := by
  rw [sum_range_id]
