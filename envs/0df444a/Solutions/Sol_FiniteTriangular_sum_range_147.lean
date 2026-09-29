-- Prove2me | solution 1 for FiniteTriangular.sum_range_147
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:23.812269+00:00
-- url     : https://prove2.me/submissions/ecbbb387-770c-490b-bc2f-37044282ae96

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 147, k = 10731 := by
  rw [sum_range_id]
