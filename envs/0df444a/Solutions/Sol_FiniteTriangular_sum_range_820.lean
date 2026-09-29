-- Prove2me | solution 1 for FiniteTriangular.sum_range_820
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:31:55.340057+00:00
-- url     : https://prove2.me/submissions/32ff4efe-37f3-4875-88db-e1e3758a720e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 820, k = 335790 := by
  rw [sum_range_id]
