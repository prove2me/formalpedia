-- Prove2me | solution 1 for FiniteTriangular.sum_range_61
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:37.062254+00:00
-- url     : https://prove2.me/submissions/d5cc2bd7-c780-481d-a1aa-8011bd5c5e57

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 61, k = 1830 := by
  decide
