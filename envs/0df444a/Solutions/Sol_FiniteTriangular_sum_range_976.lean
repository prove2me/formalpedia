-- Prove2me | solution 1 for FiniteTriangular.sum_range_976
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:04:28.565057+00:00
-- url     : https://prove2.me/submissions/29e7e5b7-1752-4d69-ae1e-f3bf5aa4757f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 976, k = 475800 := by
  rw [sum_range_id]
