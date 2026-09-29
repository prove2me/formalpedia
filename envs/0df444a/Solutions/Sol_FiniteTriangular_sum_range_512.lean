-- Prove2me | solution 1 for FiniteTriangular.sum_range_512
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:24.353994+00:00
-- url     : https://prove2.me/submissions/2a15b633-d172-454e-8f0f-5f47d66b4e84

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 512, k = 130816 := by
  rw [sum_range_id]
