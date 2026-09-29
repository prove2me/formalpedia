-- Prove2me | solution 1 for FiniteTriangular.sum_range_113
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:16.953703+00:00
-- url     : https://prove2.me/submissions/7b3767cb-0049-4b7b-b573-ab63fbcf6d98

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 113, k = 6328 := by
  decide
