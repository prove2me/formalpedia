-- Prove2me | solution 1 for FiniteTriangular.sum_range_835
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:20.731983+00:00
-- url     : https://prove2.me/submissions/a095cf34-f174-439c-97dc-392ec1d715d7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 835, k = 348195 := by
  rw [sum_range_id]
