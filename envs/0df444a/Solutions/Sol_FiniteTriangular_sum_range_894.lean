-- Prove2me | solution 1 for FiniteTriangular.sum_range_894
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:09.328625+00:00
-- url     : https://prove2.me/submissions/a49b6578-31f9-4318-88a8-591a6b43da5e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 894, k = 399171 := by
  rw [sum_range_id]
