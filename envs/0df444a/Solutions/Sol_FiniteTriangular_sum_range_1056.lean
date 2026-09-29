-- Prove2me | solution 1 for FiniteTriangular.sum_range_1056
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:15:04.810285+00:00
-- url     : https://prove2.me/submissions/a7e1632c-bab0-45a3-9ca2-0b320e551d8b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1056, k = 557040 := by
  rw [sum_range_id]
