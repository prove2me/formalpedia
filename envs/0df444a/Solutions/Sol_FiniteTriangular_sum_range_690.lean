-- Prove2me | solution 1 for FiniteTriangular.sum_range_690
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:37.42213+00:00
-- url     : https://prove2.me/submissions/141fc217-b6c7-470d-9ff0-701679d624d4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 690, k = 237705 := by
  rw [sum_range_id]
