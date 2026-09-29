-- Prove2me | solution 1 for FiniteTriangular.sum_range_42
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:18.128094+00:00
-- url     : https://prove2.me/submissions/93098072-ab92-46b1-b7da-c8f269138ec8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 42, k = 861 := by
  decide
