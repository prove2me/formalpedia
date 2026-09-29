-- Prove2me | solution 1 for FiniteTriangular.sum_range_1075
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:31.541192+00:00
-- url     : https://prove2.me/submissions/7b92a772-4bb8-40ea-9c80-37a566b2b95e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1075, k = 577275 := by
  rw [sum_range_id]
