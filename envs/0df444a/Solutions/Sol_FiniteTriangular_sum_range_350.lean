-- Prove2me | solution 1 for FiniteTriangular.sum_range_350
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:52.222336+00:00
-- url     : https://prove2.me/submissions/b221809d-2486-449c-9132-020924047dc8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 350, k = 61075 := by
  rw [sum_range_id]
