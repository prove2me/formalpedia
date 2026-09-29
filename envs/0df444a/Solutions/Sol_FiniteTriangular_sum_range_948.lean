-- Prove2me | solution 1 for FiniteTriangular.sum_range_948
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:08.440269+00:00
-- url     : https://prove2.me/submissions/7ec263ea-1733-41e9-80bc-f2dc7995c484

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 948, k = 448878 := by
  rw [sum_range_id]
