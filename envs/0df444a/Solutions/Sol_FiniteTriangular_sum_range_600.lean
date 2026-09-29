-- Prove2me | solution 1 for FiniteTriangular.sum_range_600
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:12.332471+00:00
-- url     : https://prove2.me/submissions/cc0f9e12-757d-4bbd-adb3-568900435efc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 600, k = 179700 := by
  rw [sum_range_id]
