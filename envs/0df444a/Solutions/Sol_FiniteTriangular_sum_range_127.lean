-- Prove2me | solution 1 for FiniteTriangular.sum_range_127
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:24.238203+00:00
-- url     : https://prove2.me/submissions/92a255fe-b7e5-4ae0-b9ff-b60235b869da

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 127, k = 8001 := by
  rw [sum_range_id]
