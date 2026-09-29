-- Prove2me | solution 1 for FiniteTriangular.sum_range_706
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:06:56.992296+00:00
-- url     : https://prove2.me/submissions/a7e7eb6f-297f-4e4e-ab31-f749227dc5ea

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 706, k = 248865 := by
  rw [sum_range_id]
