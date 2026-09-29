-- Prove2me | solution 1 for FiniteTriangular.sum_range_366
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:24.456164+00:00
-- url     : https://prove2.me/submissions/ca5a457c-470e-4e1b-9d25-b83f0a489b50

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 366, k = 66795 := by
  rw [sum_range_id]
