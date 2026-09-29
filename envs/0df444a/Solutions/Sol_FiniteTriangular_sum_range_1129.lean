-- Prove2me | solution 1 for FiniteTriangular.sum_range_1129
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:32:21.44412+00:00
-- url     : https://prove2.me/submissions/60125524-5722-4617-bb40-d93eda84e303

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1129, k = 636756 := by
  rw [sum_range_id]
