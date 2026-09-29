-- Prove2me | solution 1 for FiniteTriangular.sum_range_665
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:22.547783+00:00
-- url     : https://prove2.me/submissions/a51f77f0-da55-4998-9578-58c76c16735f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 665, k = 220780 := by
  rw [sum_range_id]
