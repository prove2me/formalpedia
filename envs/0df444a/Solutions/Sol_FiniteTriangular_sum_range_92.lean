-- Prove2me | solution 1 for FiniteTriangular.sum_range_92
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:52.109454+00:00
-- url     : https://prove2.me/submissions/beb41b16-1662-417a-8ca4-3195a5baa54b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 92, k = 4186 := by
  decide
