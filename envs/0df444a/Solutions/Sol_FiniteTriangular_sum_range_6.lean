-- Prove2me | solution 1 for FiniteTriangular.sum_range_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:08.092366+00:00
-- url     : https://prove2.me/submissions/0a82d0e5-a319-4e1b-a4d6-740d35d9fc9d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 6, k = 15 := by
  decide
