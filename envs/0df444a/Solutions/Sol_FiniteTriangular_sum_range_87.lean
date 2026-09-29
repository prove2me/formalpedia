-- Prove2me | solution 1 for FiniteTriangular.sum_range_87
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:18.623887+00:00
-- url     : https://prove2.me/submissions/bccbd6f5-4516-4ee9-84b4-4bda74cbea5e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 87, k = 3741 := by
  decide
