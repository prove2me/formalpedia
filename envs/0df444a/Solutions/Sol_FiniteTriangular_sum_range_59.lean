-- Prove2me | solution 1 for FiniteTriangular.sum_range_59
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:35.061198+00:00
-- url     : https://prove2.me/submissions/de993bb4-58cc-4cc4-8f9c-dbefd0ccb7d1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 59, k = 1711 := by
  decide
