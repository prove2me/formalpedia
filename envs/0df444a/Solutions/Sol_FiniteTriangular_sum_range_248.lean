-- Prove2me | solution 1 for FiniteTriangular.sum_range_248
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:27.797485+00:00
-- url     : https://prove2.me/submissions/d732068c-f8eb-49b8-a11f-944fe8ee3a9d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 248, k = 30628 := by
  rw [sum_range_id]
