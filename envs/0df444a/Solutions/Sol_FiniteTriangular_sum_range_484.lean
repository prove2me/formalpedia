-- Prove2me | solution 1 for FiniteTriangular.sum_range_484
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:22.422687+00:00
-- url     : https://prove2.me/submissions/3fdd0842-3297-4aca-ba35-20761111c2f2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 484, k = 116886 := by
  rw [sum_range_id]
