-- Prove2me | solution 1 for FiniteTriangular.sum_range_110
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:26.661992+00:00
-- url     : https://prove2.me/submissions/c2d840a4-fd6f-4afe-a426-adfb54f0049c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 110, k = 5995 := by
  decide
