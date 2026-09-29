-- Prove2me | solution 1 for FiniteTriangular.sum_range_331
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:18.187326+00:00
-- url     : https://prove2.me/submissions/d57e0823-9250-40fb-ad4d-e61ccacece76

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 331, k = 54615 := by
  rw [sum_range_id]
