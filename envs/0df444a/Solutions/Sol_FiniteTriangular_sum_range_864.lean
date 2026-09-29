-- Prove2me | solution 1 for FiniteTriangular.sum_range_864
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:14.164519+00:00
-- url     : https://prove2.me/submissions/8b7a79a7-f352-4a9a-b399-ab6c0a86b023

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 864, k = 372816 := by
  rw [sum_range_id]
