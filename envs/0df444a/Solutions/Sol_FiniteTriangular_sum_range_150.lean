-- Prove2me | solution 1 for FiniteTriangular.sum_range_150
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:44.785502+00:00
-- url     : https://prove2.me/submissions/b673d54c-a561-468d-8ea0-241741f9bee1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 150, k = 11175 := by
  rw [sum_range_id]
