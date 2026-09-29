-- Prove2me | solution 1 for FiniteTriangular.sum_range_498
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:34.123689+00:00
-- url     : https://prove2.me/submissions/8572145b-27d2-452b-ab5f-731eceab9310

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 498, k = 123753 := by
  rw [sum_range_id]
