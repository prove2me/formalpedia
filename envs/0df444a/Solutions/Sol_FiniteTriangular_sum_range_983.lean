-- Prove2me | solution 1 for FiniteTriangular.sum_range_983
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:13.687977+00:00
-- url     : https://prove2.me/submissions/5257931b-9566-4966-856f-41bc37de83f0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 983, k = 482653 := by
  rw [sum_range_id]
