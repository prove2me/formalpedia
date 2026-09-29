-- Prove2me | solution 1 for FiniteTriangular.sum_range_231
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:14.895036+00:00
-- url     : https://prove2.me/submissions/f627133d-bceb-407c-ac25-3da600d2b9a0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 231, k = 26565 := by
  rw [sum_range_id]
