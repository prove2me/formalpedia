-- Prove2me | solution 1 for FiniteTriangular.sum_range_199
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:35.317448+00:00
-- url     : https://prove2.me/submissions/551d9d1b-f066-4218-a794-de6d4540fea8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 199, k = 19701 := by
  rw [sum_range_id]
