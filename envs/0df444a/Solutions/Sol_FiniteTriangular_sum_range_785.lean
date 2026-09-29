-- Prove2me | solution 1 for FiniteTriangular.sum_range_785
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:05.503256+00:00
-- url     : https://prove2.me/submissions/1fb05026-4d6c-4ed1-8227-111cfcca5599

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 785, k = 307720 := by
  rw [sum_range_id]
