-- Prove2me | solution 1 for FiniteTriangular.sum_range_550
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:30:58.61217+00:00
-- url     : https://prove2.me/submissions/66c688a7-df86-4020-84c0-5919d154daa0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 550, k = 150975 := by
  rw [sum_range_id]
