-- Prove2me | solution 1 for FiniteTriangular.sum_range_376
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:19.189237+00:00
-- url     : https://prove2.me/submissions/65f2e31c-ec66-469d-a7d9-ab627f0de9a0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 376, k = 70500 := by
  rw [sum_range_id]
