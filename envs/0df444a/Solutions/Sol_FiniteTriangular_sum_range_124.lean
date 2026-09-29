-- Prove2me | solution 1 for FiniteTriangular.sum_range_124
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:22.038178+00:00
-- url     : https://prove2.me/submissions/6f9f7d70-1a58-468c-8f70-23ca511a35da

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 124, k = 7626 := by
  rw [sum_range_id]
