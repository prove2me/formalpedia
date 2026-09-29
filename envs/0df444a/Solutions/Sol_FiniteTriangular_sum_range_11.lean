-- Prove2me | solution 1 for FiniteTriangular.sum_range_11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:06.792459+00:00
-- url     : https://prove2.me/submissions/c4fdef9e-c0c4-4a67-817f-8e83c678bdac

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 11, k = 55 := by
  decide
