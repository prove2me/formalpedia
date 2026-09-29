-- Prove2me | solution 1 for FiniteTriangular.sum_range_996
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:38:49.070412+00:00
-- url     : https://prove2.me/submissions/e63491bc-2881-4aba-b93e-d0f4934bdfe8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 996, k = 495510 := by
  rw [sum_range_id]
