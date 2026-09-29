-- Prove2me | solution 1 for FiniteTriangular.sum_range_1083
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:26.795791+00:00
-- url     : https://prove2.me/submissions/59e04f84-68f3-42e8-9ec8-e5c4e9020a83

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1083, k = 585903 := by
  rw [sum_range_id]
