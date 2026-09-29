-- Prove2me | solution 1 for FiniteTriangular.sum_range_1121
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:40.613143+00:00
-- url     : https://prove2.me/submissions/cb6f8260-be7b-4c6f-b64d-3972706296cf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1121, k = 627760 := by
  rw [sum_range_id]
