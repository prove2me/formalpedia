-- Prove2me | solution 1 for FiniteTriangular.sum_range_1058
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:00.821784+00:00
-- url     : https://prove2.me/submissions/0379914b-b9a9-423d-8d8c-495477e30484

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1058, k = 559153 := by
  rw [sum_range_id]
