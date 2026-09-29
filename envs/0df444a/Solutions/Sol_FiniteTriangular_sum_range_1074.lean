-- Prove2me | solution 1 for FiniteTriangular.sum_range_1074
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:30.92421+00:00
-- url     : https://prove2.me/submissions/cb31db97-2827-45c2-9213-1eeef2613775

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1074, k = 576201 := by
  rw [sum_range_id]
