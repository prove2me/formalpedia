-- Prove2me | solution 1 for FiniteTriangular.sum_range_356
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:28.382975+00:00
-- url     : https://prove2.me/submissions/d2c8895d-0d29-4934-8b68-39a77a6a307f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 356, k = 63190 := by
  rw [sum_range_id]
