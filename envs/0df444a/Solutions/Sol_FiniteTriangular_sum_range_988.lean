-- Prove2me | solution 1 for FiniteTriangular.sum_range_988
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:05.644985+00:00
-- url     : https://prove2.me/submissions/83332f8f-0a9e-4869-b6ba-ea9182267b91

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 988, k = 487578 := by
  rw [sum_range_id]
