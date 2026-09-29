-- Prove2me | solution 1 for FiniteTriangular.sum_range_698
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:10.190805+00:00
-- url     : https://prove2.me/submissions/375da0a4-492b-4a3f-8737-62f6d0853781

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 698, k = 243253 := by
  rw [sum_range_id]
