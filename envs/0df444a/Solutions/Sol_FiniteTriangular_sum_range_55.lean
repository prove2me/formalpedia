-- Prove2me | solution 1 for FiniteTriangular.sum_range_55
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:15.401683+00:00
-- url     : https://prove2.me/submissions/4b96cdaa-fcc4-4d11-8eaa-fc2c420447f3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 55, k = 1485 := by
  decide
