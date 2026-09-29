-- Prove2me | solution 1 for FiniteTriangular.sum_range_620
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:20.384909+00:00
-- url     : https://prove2.me/submissions/8420a1b1-f4b9-41be-8288-9c12d5fe3f9d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 620, k = 191890 := by
  rw [sum_range_id]
