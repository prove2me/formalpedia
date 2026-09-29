-- Prove2me | solution 1 for FiniteTriangular.sum_range_26
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:13.969137+00:00
-- url     : https://prove2.me/submissions/5b2d0cb3-2625-41f6-bf4a-f0475b1cbb4b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 26, k = 325 := by
  decide
