-- Prove2me | solution 1 for FiniteTriangular.sum_range_266
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:12:58.928017+00:00
-- url     : https://prove2.me/submissions/0282ce83-f58e-4839-bc7c-39bb9fc20746

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 266, k = 35245 := by
  rw [sum_range_id]
