-- Prove2me | solution 1 for FiniteTriangular.sum_range_798
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:46.330157+00:00
-- url     : https://prove2.me/submissions/63a515da-1f48-4772-8391-16e1719f89e9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 798, k = 318003 := by
  rw [sum_range_id]
