-- Prove2me | solution 1 for FiniteTriangular.sum_range_198
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:34.672976+00:00
-- url     : https://prove2.me/submissions/6d308d5e-f60b-4d5c-b235-338e2e80e533

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 198, k = 19503 := by
  rw [sum_range_id]
