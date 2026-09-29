-- Prove2me | solution 1 for FiniteTriangular.sum_range_52
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:12.624987+00:00
-- url     : https://prove2.me/submissions/37522a4a-ff6c-40b8-837c-e21dada8d712

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 52, k = 1326 := by
  decide
