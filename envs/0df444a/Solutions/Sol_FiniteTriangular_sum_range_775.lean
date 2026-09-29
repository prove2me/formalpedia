-- Prove2me | solution 1 for FiniteTriangular.sum_range_775
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:40.352346+00:00
-- url     : https://prove2.me/submissions/4fecaa17-ea61-45a4-b80b-9103a94f1796

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 775, k = 299925 := by
  rw [sum_range_id]
