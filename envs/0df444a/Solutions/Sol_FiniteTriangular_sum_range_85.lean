-- Prove2me | solution 1 for FiniteTriangular.sum_range_85
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:15.61727+00:00
-- url     : https://prove2.me/submissions/c633fae5-226a-4d64-a046-3f1e15711ea3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 85, k = 3570 := by
  decide
