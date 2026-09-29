-- Prove2me | solution 1 for FiniteTriangular.sum_range_489
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:18:56.773723+00:00
-- url     : https://prove2.me/submissions/cf2830ca-1f69-455d-afc4-57b347089db2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 489, k = 119316 := by
  rw [sum_range_id]
