-- Prove2me | solution 1 for FiniteTriangular.sum_range_339
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:05.068123+00:00
-- url     : https://prove2.me/submissions/a56c7903-0e4e-4731-ac4b-5e9bdf7f0f1b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 339, k = 57291 := by
  rw [sum_range_id]
