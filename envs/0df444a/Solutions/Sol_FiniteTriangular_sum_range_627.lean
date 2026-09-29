-- Prove2me | solution 1 for FiniteTriangular.sum_range_627
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:04.265983+00:00
-- url     : https://prove2.me/submissions/7a349f8e-ee35-4da2-84d6-f9c27b792306

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 627, k = 196251 := by
  rw [sum_range_id]
