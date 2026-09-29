-- Prove2me | solution 1 for FiniteTriangular.sum_range_1107
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:31.852496+00:00
-- url     : https://prove2.me/submissions/cd32309a-f838-436e-9cef-4d234006f9d8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1107, k = 612171 := by
  rw [sum_range_id]
