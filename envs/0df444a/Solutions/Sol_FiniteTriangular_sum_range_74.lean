-- Prove2me | solution 1 for FiniteTriangular.sum_range_74
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:19.118303+00:00
-- url     : https://prove2.me/submissions/80be9e23-d78b-4b5e-8726-4f26bef17428

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 74, k = 2701 := by
  decide
