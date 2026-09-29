-- Prove2me | solution 1 for FiniteTriangular.sum_range_184
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:24:30.214251+00:00
-- url     : https://prove2.me/submissions/7f836f43-8252-48be-8e34-967281ff656d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 184, k = 16836 := by
  rw [sum_range_id]
