-- Prove2me | solution 1 for FiniteTriangular.sum_range_190
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:19.992279+00:00
-- url     : https://prove2.me/submissions/2b9b83e5-7ec9-415e-9bc9-651a008779f0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 190, k = 17955 := by
  rw [sum_range_id]
