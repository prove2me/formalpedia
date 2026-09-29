-- Prove2me | solution 1 for FiniteTriangular.sum_range_999
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:51.045286+00:00
-- url     : https://prove2.me/submissions/50975b5d-629e-4b05-bc8f-6923b79c70b1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 999, k = 498501 := by
  rw [sum_range_id]
