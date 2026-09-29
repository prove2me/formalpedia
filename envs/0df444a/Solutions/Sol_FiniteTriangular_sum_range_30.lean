-- Prove2me | solution 1 for FiniteTriangular.sum_range_30
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:16.757898+00:00
-- url     : https://prove2.me/submissions/0fb2fe72-6cd3-47af-9c57-c21c466b954d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 30, k = 435 := by
  decide
