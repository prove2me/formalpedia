-- Prove2me | solution 1 for FiniteTriangular.sum_range_16
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:11.823262+00:00
-- url     : https://prove2.me/submissions/38b7fd87-e222-4bc9-934e-b6204eebe69a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 16, k = 120 := by
  decide
