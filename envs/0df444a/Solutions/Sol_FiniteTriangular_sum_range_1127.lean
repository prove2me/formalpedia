-- Prove2me | solution 1 for FiniteTriangular.sum_range_1127
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:44.758008+00:00
-- url     : https://prove2.me/submissions/72a620f0-67e8-4f71-91dd-e33e89be6fc6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1127, k = 634501 := by
  rw [sum_range_id]
