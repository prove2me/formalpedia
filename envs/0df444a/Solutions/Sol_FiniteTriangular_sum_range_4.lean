-- Prove2me | solution 1 for FiniteTriangular.sum_range_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:07.306344+00:00
-- url     : https://prove2.me/submissions/e79e0857-6b1f-418b-b55f-80750198ae8c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 4, k = 6 := by
  decide
