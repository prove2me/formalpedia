-- Prove2me | solution 1 for FiniteTriangular.sum_range_803
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:31.869458+00:00
-- url     : https://prove2.me/submissions/a8722155-85d8-43f8-a851-bd8bdfa5cb78

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 803, k = 322003 := by
  rw [sum_range_id]
