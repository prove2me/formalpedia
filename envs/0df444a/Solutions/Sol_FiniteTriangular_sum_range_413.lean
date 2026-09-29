-- Prove2me | solution 1 for FiniteTriangular.sum_range_413
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:18.706866+00:00
-- url     : https://prove2.me/submissions/f7ce07a9-ecc2-4f9f-875d-f4e4ef97d34d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 413, k = 85078 := by
  rw [sum_range_id]
