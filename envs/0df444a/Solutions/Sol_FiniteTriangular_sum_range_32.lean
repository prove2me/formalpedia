-- Prove2me | solution 1 for FiniteTriangular.sum_range_32
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:18.266992+00:00
-- url     : https://prove2.me/submissions/cc762ad6-66ab-4024-a3e2-83878cbb2740

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 32, k = 496 := by
  decide
