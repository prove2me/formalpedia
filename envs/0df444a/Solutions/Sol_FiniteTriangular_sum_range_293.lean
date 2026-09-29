-- Prove2me | solution 1 for FiniteTriangular.sum_range_293
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:19.871257+00:00
-- url     : https://prove2.me/submissions/dcc46c86-ce05-4402-97cd-d45cbbc86cc4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 293, k = 42778 := by
  rw [sum_range_id]
