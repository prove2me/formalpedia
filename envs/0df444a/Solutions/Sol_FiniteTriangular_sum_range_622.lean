-- Prove2me | solution 1 for FiniteTriangular.sum_range_622
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:21.556983+00:00
-- url     : https://prove2.me/submissions/5f21e25d-8843-409b-bb8b-fa4582112b6c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 622, k = 193131 := by
  rw [sum_range_id]
