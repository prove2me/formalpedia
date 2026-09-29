-- Prove2me | solution 1 for FiniteTriangular.sum_range_624
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:22.800418+00:00
-- url     : https://prove2.me/submissions/3860d00a-759e-4f74-a188-d2d7da8f0e4a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 624, k = 194376 := by
  rw [sum_range_id]
