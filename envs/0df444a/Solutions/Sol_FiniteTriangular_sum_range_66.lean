-- Prove2me | solution 1 for FiniteTriangular.sum_range_66
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:01.05499+00:00
-- url     : https://prove2.me/submissions/f802e2de-4eb3-442b-97cf-d497c130058c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 66, k = 2145 := by
  decide
