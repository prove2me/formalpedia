-- Prove2me | solution 1 for FiniteTriangular.sum_range_60
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:35.960984+00:00
-- url     : https://prove2.me/submissions/83212d6a-4d70-4091-a005-e16856911ee6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 60, k = 1770 := by
  decide
