-- Prove2me | solution 1 for FiniteTriangular.sum_range_48
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:22.936841+00:00
-- url     : https://prove2.me/submissions/b39dbad3-84b7-49cb-8bf6-a0dfcce9cef8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 48, k = 1128 := by
  decide
