-- Prove2me | solution 1 for FiniteTriangular.sum_range_72
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:07.386245+00:00
-- url     : https://prove2.me/submissions/4ae0d9ae-65d6-484d-9f65-0235ff7254a4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 72, k = 2556 := by
  decide
