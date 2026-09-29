-- Prove2me | solution 1 for FiniteTriangular.sum_range_323
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:30.18955+00:00
-- url     : https://prove2.me/submissions/332931c3-0705-48ed-97fd-92cf7ef79d9d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 323, k = 52003 := by
  rw [sum_range_id]
