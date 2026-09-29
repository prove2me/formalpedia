-- Prove2me | solution 1 for FiniteTriangular.sum_range_1071
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:18:50.34918+00:00
-- url     : https://prove2.me/submissions/64bb2e13-8cc0-496e-872d-473338d7721b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1071, k = 572985 := by
  rw [sum_range_id]
