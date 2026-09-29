-- Prove2me | solution 1 for FiniteTriangular.sum_range_41
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:17.958529+00:00
-- url     : https://prove2.me/submissions/1acc57cc-bf5f-4312-866a-2093f45fc3e6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 41, k = 820 := by
  decide
