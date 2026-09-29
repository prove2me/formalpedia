-- Prove2me | solution 1 for FiniteTriangular.sum_range_263
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:16.680629+00:00
-- url     : https://prove2.me/submissions/1e49ef22-ae64-49f5-9f03-6f464a7a8e34

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 263, k = 34453 := by
  rw [sum_range_id]
