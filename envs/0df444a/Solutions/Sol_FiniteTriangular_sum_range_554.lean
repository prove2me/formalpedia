-- Prove2me | solution 1 for FiniteTriangular.sum_range_554
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:25.213796+00:00
-- url     : https://prove2.me/submissions/9b4198c2-18a1-458b-b919-7437d34b967f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 554, k = 153181 := by
  rw [sum_range_id]
