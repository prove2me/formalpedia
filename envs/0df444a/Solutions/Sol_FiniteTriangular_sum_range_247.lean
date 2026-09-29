-- Prove2me | solution 1 for FiniteTriangular.sum_range_247
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:27.056294+00:00
-- url     : https://prove2.me/submissions/f6e08b1e-0fb8-4b23-a0c9-b6adf49ae048

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 247, k = 30381 := by
  rw [sum_range_id]
