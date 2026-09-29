-- Prove2me | solution 1 for FiniteTriangular.sum_range_1053
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:15:02.098829+00:00
-- url     : https://prove2.me/submissions/a2cb9c71-da7c-4243-8029-2a49a4fca59e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1053, k = 553878 := by
  rw [sum_range_id]
