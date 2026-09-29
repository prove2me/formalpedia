-- Prove2me | solution 1 for FiniteTriangular.sum_range_730
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:44.254926+00:00
-- url     : https://prove2.me/submissions/9b115e56-dec7-4d7d-94f9-33c99bda153a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 730, k = 266085 := by
  rw [sum_range_id]
