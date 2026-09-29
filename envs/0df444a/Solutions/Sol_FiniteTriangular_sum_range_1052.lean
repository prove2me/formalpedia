-- Prove2me | solution 1 for FiniteTriangular.sum_range_1052
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:15:01.281981+00:00
-- url     : https://prove2.me/submissions/985f413c-b0e9-4b61-b648-bf7947a6bc11

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1052, k = 552826 := by
  rw [sum_range_id]
