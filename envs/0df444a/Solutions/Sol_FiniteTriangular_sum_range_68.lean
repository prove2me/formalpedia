-- Prove2me | solution 1 for FiniteTriangular.sum_range_68
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:03.513561+00:00
-- url     : https://prove2.me/submissions/b5bde600-095e-4f9e-aafb-9e39b0dfb06c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 68, k = 2278 := by
  decide
