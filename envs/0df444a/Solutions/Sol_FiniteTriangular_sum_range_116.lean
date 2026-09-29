-- Prove2me | solution 1 for FiniteTriangular.sum_range_116
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:19.277463+00:00
-- url     : https://prove2.me/submissions/647db466-a578-48c1-bb22-33aefe9f3eaf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 116, k = 6670 := by
  decide
