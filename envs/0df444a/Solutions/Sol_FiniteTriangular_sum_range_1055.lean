-- Prove2me | solution 1 for FiniteTriangular.sum_range_1055
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:15:03.977143+00:00
-- url     : https://prove2.me/submissions/ce991a0b-176f-4334-9066-1904117c1d52

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1055, k = 555985 := by
  rw [sum_range_id]
