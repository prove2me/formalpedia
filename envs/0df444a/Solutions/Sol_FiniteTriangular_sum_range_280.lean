-- Prove2me | solution 1 for FiniteTriangular.sum_range_280
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:56.77113+00:00
-- url     : https://prove2.me/submissions/61b407b5-5adf-425c-97ef-03856ea8d31e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 280, k = 39060 := by
  rw [sum_range_id]
