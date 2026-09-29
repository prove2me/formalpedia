-- Prove2me | solution 1 for FiniteTriangular.sum_range_614
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:44.836129+00:00
-- url     : https://prove2.me/submissions/0e538d71-0a92-437b-ad14-6428f2fd59b8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 614, k = 188191 := by
  rw [sum_range_id]
