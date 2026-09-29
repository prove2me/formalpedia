-- Prove2me | solution 1 for FiniteTriangular.sum_range_1087
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:30.408435+00:00
-- url     : https://prove2.me/submissions/18d7f557-bfeb-4884-b6a4-54ef84a26288

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1087, k = 590241 := by
  rw [sum_range_id]
