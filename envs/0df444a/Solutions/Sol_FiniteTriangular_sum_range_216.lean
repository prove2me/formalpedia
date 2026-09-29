-- Prove2me | solution 1 for FiniteTriangular.sum_range_216
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:45.225572+00:00
-- url     : https://prove2.me/submissions/3549e176-1b1e-4fe4-88b7-e888c9111b59

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 216, k = 23220 := by
  rw [sum_range_id]
