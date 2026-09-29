-- Prove2me | solution 1 for FiniteTriangular.sum_range_206
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:30.157901+00:00
-- url     : https://prove2.me/submissions/c67e588a-6b65-448c-bbdf-371708ab4ff3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 206, k = 21115 := by
  rw [sum_range_id]
