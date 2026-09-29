-- Prove2me | solution 1 for FiniteTriangular.sum_range_111
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:27.462846+00:00
-- url     : https://prove2.me/submissions/faf868dd-133c-47b5-bf1c-6e27d1688a4d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 111, k = 6105 := by
  decide
