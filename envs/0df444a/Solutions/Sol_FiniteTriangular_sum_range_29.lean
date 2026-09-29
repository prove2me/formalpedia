-- Prove2me | solution 1 for FiniteTriangular.sum_range_29
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:16.028445+00:00
-- url     : https://prove2.me/submissions/a159bee0-3c69-4e5c-8f78-8dd86af07ec4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 29, k = 406 := by
  decide
