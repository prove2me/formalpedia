-- Prove2me | solution 1 for FiniteTriangular.sum_range_148
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:43.142852+00:00
-- url     : https://prove2.me/submissions/99f6c35d-7ff6-4805-a129-6adab0aed53c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 148, k = 10878 := by
  rw [sum_range_id]
