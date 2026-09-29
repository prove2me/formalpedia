-- Prove2me | solution 1 for FiniteTriangular.sum_range_219
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:26.689674+00:00
-- url     : https://prove2.me/submissions/56cc8e79-2c3e-4168-b3e0-b2b4f5b29271

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 219, k = 23871 := by
  rw [sum_range_id]
