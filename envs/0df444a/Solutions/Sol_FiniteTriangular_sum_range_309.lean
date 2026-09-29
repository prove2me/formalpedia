-- Prove2me | solution 1 for FiniteTriangular.sum_range_309
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:07.053466+00:00
-- url     : https://prove2.me/submissions/31b2cbdd-3a8d-46f2-afbc-b1574d0c70a0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 309, k = 47586 := by
  rw [sum_range_id]
