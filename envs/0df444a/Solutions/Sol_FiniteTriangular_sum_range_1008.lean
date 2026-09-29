-- Prove2me | solution 1 for FiniteTriangular.sum_range_1008
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:40:53.304319+00:00
-- url     : https://prove2.me/submissions/eda62c85-4d0f-4231-aaf1-c994e03fe1fb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1008, k = 507528 := by
  rw [sum_range_id]
