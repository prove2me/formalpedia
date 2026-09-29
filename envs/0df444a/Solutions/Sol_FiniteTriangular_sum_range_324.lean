-- Prove2me | solution 1 for FiniteTriangular.sum_range_324
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:31.954346+00:00
-- url     : https://prove2.me/submissions/e06e9176-2787-420a-a881-a13229b0ecbd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 324, k = 52326 := by
  rw [sum_range_id]
