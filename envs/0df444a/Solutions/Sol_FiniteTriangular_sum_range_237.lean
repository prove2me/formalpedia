-- Prove2me | solution 1 for FiniteTriangular.sum_range_237
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:45.872582+00:00
-- url     : https://prove2.me/submissions/f9184587-5995-478b-b1e8-4f2a8b10afb4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 237, k = 27966 := by
  rw [sum_range_id]
