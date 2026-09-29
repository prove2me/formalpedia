-- Prove2me | solution 1 for FiniteTriangular.sum_range_320
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:38.705643+00:00
-- url     : https://prove2.me/submissions/e6769f5a-786e-4939-9c70-e51e1984f46b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 320, k = 51040 := by
  rw [sum_range_id]
