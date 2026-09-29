-- Prove2me | solution 1 for FiniteTriangular.sum_range_494
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:18:59.940134+00:00
-- url     : https://prove2.me/submissions/0fc6928c-5061-4183-9d4e-d3a8f9517783

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 494, k = 121771 := by
  rw [sum_range_id]
