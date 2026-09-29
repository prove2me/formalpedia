-- Prove2me | solution 1 for FiniteTriangular.sum_range_28
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:15.40263+00:00
-- url     : https://prove2.me/submissions/49523f8c-dc94-436b-8e30-15c1a5b0b124

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 28, k = 378 := by
  decide
