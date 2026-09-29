-- Prove2me | solution 1 for FiniteTriangular.sum_range_825
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:39.76146+00:00
-- url     : https://prove2.me/submissions/96f997aa-3e27-4361-9527-089522e38198

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 825, k = 339900 := by
  rw [sum_range_id]
