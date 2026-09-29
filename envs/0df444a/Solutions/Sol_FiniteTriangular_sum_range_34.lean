-- Prove2me | solution 1 for FiniteTriangular.sum_range_34
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:10.040137+00:00
-- url     : https://prove2.me/submissions/71e74adf-2485-428d-b3dd-feb7105f397d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 34, k = 561 := by
  decide
