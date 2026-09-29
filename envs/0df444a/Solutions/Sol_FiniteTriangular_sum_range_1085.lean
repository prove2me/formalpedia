-- Prove2me | solution 1 for FiniteTriangular.sum_range_1085
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:28.022278+00:00
-- url     : https://prove2.me/submissions/d9fcac95-04f0-4ccb-adac-999f7bf1c23d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1085, k = 588070 := by
  rw [sum_range_id]
