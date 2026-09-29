-- Prove2me | solution 1 for FiniteTriangular.sum_range_1118
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:08.558249+00:00
-- url     : https://prove2.me/submissions/6700ffdd-b5c9-4910-a33f-513907a77e3d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1118, k = 624403 := by
  rw [sum_range_id]
