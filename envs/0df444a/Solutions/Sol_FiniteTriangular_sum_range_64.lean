-- Prove2me | solution 1 for FiniteTriangular.sum_range_64
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:39.19581+00:00
-- url     : https://prove2.me/submissions/fc353aee-fe7d-4a63-80a0-a7cf3e1d6505

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 64, k = 2016 := by
  decide
