-- Prove2me | solution 1 for FiniteTriangular.sum_range_268
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:13:00.181966+00:00
-- url     : https://prove2.me/submissions/f0d4454d-69a0-4748-bf1e-c61b81344136

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 268, k = 35778 := by
  rw [sum_range_id]
