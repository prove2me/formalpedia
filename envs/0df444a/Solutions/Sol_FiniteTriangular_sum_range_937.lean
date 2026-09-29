-- Prove2me | solution 1 for FiniteTriangular.sum_range_937
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:09.558689+00:00
-- url     : https://prove2.me/submissions/e9fb4c8e-c33a-4dd6-a9c7-4a0c91a48633

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 937, k = 438516 := by
  rw [sum_range_id]
