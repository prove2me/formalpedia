-- Prove2me | solution 1 for FiniteTriangular.sum_range_141
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:18.943983+00:00
-- url     : https://prove2.me/submissions/e58e24d0-1729-4a3f-b915-d22822465ccd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 141, k = 9870 := by
  rw [sum_range_id]
