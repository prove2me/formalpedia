-- Prove2me | solution 1 for FiniteTriangular.sum_range_502
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:36.519875+00:00
-- url     : https://prove2.me/submissions/89fee6c7-6eaa-43aa-a8af-b9a35c633b28

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 502, k = 125751 := by
  rw [sum_range_id]
