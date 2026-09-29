-- Prove2me | solution 1 for FiniteTriangular.sum_range_609
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:41.4052+00:00
-- url     : https://prove2.me/submissions/1767e86c-5039-436c-91b1-a67280fffb08

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 609, k = 185136 := by
  rw [sum_range_id]
