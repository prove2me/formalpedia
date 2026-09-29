-- Prove2me | solution 1 for FiniteTriangular.sum_range_428
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:51.33201+00:00
-- url     : https://prove2.me/submissions/8166ec7d-ea31-4d8a-ac10-ea44afbc56d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 428, k = 91378 := by
  rw [sum_range_id]
