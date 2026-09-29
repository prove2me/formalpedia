-- Prove2me | solution 1 for FiniteTriangular.sum_range_86
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:17.607897+00:00
-- url     : https://prove2.me/submissions/250171b0-f32f-40eb-b7c1-ad0e3d8bd7f0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 86, k = 3655 := by
  decide
