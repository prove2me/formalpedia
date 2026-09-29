-- Prove2me | solution 1 for FiniteTriangular.sum_range_780
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:23.610801+00:00
-- url     : https://prove2.me/submissions/4e4076cf-a473-4230-9d6c-a95c7bb36e1f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 780, k = 303810 := by
  rw [sum_range_id]
