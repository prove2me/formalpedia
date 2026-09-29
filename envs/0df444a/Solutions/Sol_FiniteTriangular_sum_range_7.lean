-- Prove2me | solution 1 for FiniteTriangular.sum_range_7
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:08.855539+00:00
-- url     : https://prove2.me/submissions/3411ac0a-3416-4d1e-93d0-7f36e1e4ff25

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 7, k = 21 := by
  decide
