-- Prove2me | solution 1 for FiniteTriangular.sum_range_630
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:06.181722+00:00
-- url     : https://prove2.me/submissions/8f7e21df-df8e-408b-9111-6d2162f9e33a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 630, k = 198135 := by
  rw [sum_range_id]
