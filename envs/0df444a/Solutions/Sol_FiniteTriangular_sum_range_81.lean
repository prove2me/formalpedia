-- Prove2me | solution 1 for FiniteTriangular.sum_range_81
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:12.629664+00:00
-- url     : https://prove2.me/submissions/378a4b76-e355-4b0f-aa76-4dede3e9ef1d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 81, k = 3240 := by
  decide
