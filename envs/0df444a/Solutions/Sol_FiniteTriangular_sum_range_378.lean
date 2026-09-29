-- Prove2me | solution 1 for FiniteTriangular.sum_range_378
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:20.626044+00:00
-- url     : https://prove2.me/submissions/2edb89e7-7efe-4482-9584-97645f7effcf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 378, k = 71253 := by
  rw [sum_range_id]
