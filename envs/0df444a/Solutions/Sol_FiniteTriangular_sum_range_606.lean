-- Prove2me | solution 1 for FiniteTriangular.sum_range_606
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:56.407241+00:00
-- url     : https://prove2.me/submissions/a06a6430-66e5-4f8a-92e1-13be0a4d3ee3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 606, k = 183315 := by
  rw [sum_range_id]
