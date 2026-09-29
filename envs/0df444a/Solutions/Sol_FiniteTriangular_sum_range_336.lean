-- Prove2me | solution 1 for FiniteTriangular.sum_range_336
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:21.469999+00:00
-- url     : https://prove2.me/submissions/d2ea3b78-1b94-4392-b3a2-7a9eeff2e0c6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 336, k = 56280 := by
  rw [sum_range_id]
