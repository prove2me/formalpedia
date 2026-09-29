-- Prove2me | solution 1 for FiniteTriangular.sum_range_120
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:23.141241+00:00
-- url     : https://prove2.me/submissions/94a6dca7-e236-436d-8c88-1887412fefae

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 120, k = 7140 := by
  decide
