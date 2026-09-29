-- Prove2me | solution 1 for FiniteTriangular.sum_range_191
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:20.607984+00:00
-- url     : https://prove2.me/submissions/9ebf5632-c9d6-4fdb-8af7-29a96eb7d60d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 191, k = 18145 := by
  rw [sum_range_id]
