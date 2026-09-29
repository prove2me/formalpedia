-- Prove2me | solution 1 for FiniteTriangular.sum_range_1017
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:08.250648+00:00
-- url     : https://prove2.me/submissions/6083d747-8687-4428-ab98-f12820bcf0fd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1017, k = 516636 := by
  rw [sum_range_id]
