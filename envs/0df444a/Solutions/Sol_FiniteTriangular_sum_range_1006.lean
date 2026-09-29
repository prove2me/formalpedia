-- Prove2me | solution 1 for FiniteTriangular.sum_range_1006
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:51.985718+00:00
-- url     : https://prove2.me/submissions/8d00370f-3ba4-4d52-89da-a9c36dc7d9ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1006, k = 505515 := by
  rw [sum_range_id]
