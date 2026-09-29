-- Prove2me | solution 1 for FiniteTriangular.sum_range_82
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:13.480218+00:00
-- url     : https://prove2.me/submissions/134c0434-be8c-4b4f-b304-482d4729d980

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 82, k = 3321 := by
  decide
