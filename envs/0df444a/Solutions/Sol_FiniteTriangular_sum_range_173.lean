-- Prove2me | solution 1 for FiniteTriangular.sum_range_173
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:16.870495+00:00
-- url     : https://prove2.me/submissions/86f02d04-aafb-4dbf-81d1-b84112801f32

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 173, k = 14878 := by
  rw [sum_range_id]
