-- Prove2me | solution 1 for FiniteTriangular.sum_range_313
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:34.057321+00:00
-- url     : https://prove2.me/submissions/b24f5540-cc5e-4b34-8cd0-0837760d8a72

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 313, k = 48828 := by
  rw [sum_range_id]
