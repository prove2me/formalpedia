-- Prove2me | solution 1 for FiniteTriangular.sum_range_409
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:16.230525+00:00
-- url     : https://prove2.me/submissions/e0809fc5-b399-4d37-9887-a3a754ad436a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 409, k = 83436 := by
  rw [sum_range_id]
