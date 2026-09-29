-- Prove2me | solution 1 for FiniteTriangular.sum_range_1038
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:58.066009+00:00
-- url     : https://prove2.me/submissions/63a5ec6b-3475-4324-b848-55bed3fe4f94

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1038, k = 538203 := by
  rw [sum_range_id]
