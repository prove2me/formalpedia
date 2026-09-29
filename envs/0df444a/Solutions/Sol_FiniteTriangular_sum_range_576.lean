-- Prove2me | solution 1 for FiniteTriangular.sum_range_576
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:07.068003+00:00
-- url     : https://prove2.me/submissions/09ee6c2c-50cf-49a1-873e-816c403b69d7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 576, k = 165600 := by
  rw [sum_range_id]
