-- Prove2me | solution 1 for FiniteTriangular.sum_range_923
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:46.049638+00:00
-- url     : https://prove2.me/submissions/974eec7d-4fac-44b0-9439-8c938f99cd8d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 923, k = 425503 := by
  rw [sum_range_id]
