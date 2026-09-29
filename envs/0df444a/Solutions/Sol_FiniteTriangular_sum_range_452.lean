-- Prove2me | solution 1 for FiniteTriangular.sum_range_452
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:01.464238+00:00
-- url     : https://prove2.me/submissions/9d15b816-bd96-4b98-9b0e-ce247a3e3e4f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 452, k = 101926 := by
  rw [sum_range_id]
