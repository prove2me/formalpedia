-- Prove2me | solution 1 for FiniteTriangular.sum_range_760
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:15.449539+00:00
-- url     : https://prove2.me/submissions/7ec69ec9-1dd2-4cbb-a40e-0ce53fb1cf9b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 760, k = 288420 := by
  rw [sum_range_id]
