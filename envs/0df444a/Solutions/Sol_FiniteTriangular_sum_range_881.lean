-- Prove2me | solution 1 for FiniteTriangular.sum_range_881
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:17.054088+00:00
-- url     : https://prove2.me/submissions/90c2493a-f6e5-4f09-8a29-7ecbd31c56cc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 881, k = 387640 := by
  rw [sum_range_id]
