-- Prove2me | solution 1 for FiniteTriangular.sum_range_933
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:34.386385+00:00
-- url     : https://prove2.me/submissions/250345fe-4110-42b0-97ae-a442ad0c7180

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 933, k = 434778 := by
  rw [sum_range_id]
