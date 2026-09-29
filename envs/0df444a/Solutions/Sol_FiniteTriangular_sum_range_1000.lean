-- Prove2me | solution 1 for FiniteTriangular.sum_range_1000
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:51.643387+00:00
-- url     : https://prove2.me/submissions/90d2ce41-e303-465a-ba3d-205dc0a1e6df

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1000, k = 499500 := by
  rw [sum_range_id]
