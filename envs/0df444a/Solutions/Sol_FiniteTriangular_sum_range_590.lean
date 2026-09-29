-- Prove2me | solution 1 for FiniteTriangular.sum_range_590
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:35.589331+00:00
-- url     : https://prove2.me/submissions/ad7449b6-58f4-496e-bf93-ff53a8235778

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 590, k = 173755 := by
  rw [sum_range_id]
