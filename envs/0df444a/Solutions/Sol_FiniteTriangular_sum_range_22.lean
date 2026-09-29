-- Prove2me | solution 1 for FiniteTriangular.sum_range_22
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:37.863688+00:00
-- url     : https://prove2.me/submissions/1c20d0ca-a000-4e2a-bd18-bf81a343e85f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 22, k = 231 := by
  decide
