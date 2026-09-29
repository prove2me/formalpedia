-- Prove2me | solution 1 for FiniteTriangular.sum_range_648
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:28.134705+00:00
-- url     : https://prove2.me/submissions/646a9055-a51d-43e2-b62b-e9a797bdb727

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 648, k = 209628 := by
  rw [sum_range_id]
