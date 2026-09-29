-- Prove2me | solution 1 for FiniteTriangular.sum_range_160
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:14.47135+00:00
-- url     : https://prove2.me/submissions/6ce37d27-2191-455c-98d6-f8272db49fba

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 160, k = 12720 := by
  rw [sum_range_id]
