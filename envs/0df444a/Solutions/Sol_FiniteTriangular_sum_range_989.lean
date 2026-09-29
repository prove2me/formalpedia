-- Prove2me | solution 1 for FiniteTriangular.sum_range_989
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:06.352737+00:00
-- url     : https://prove2.me/submissions/40523bc1-ccac-4245-8702-63cfe68b0d25

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 989, k = 488566 := by
  rw [sum_range_id]
