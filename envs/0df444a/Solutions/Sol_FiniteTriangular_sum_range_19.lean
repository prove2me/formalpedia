-- Prove2me | solution 1 for FiniteTriangular.sum_range_19
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:35.545002+00:00
-- url     : https://prove2.me/submissions/0544a93c-da44-4e05-9c9a-b6cc07787830

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 19, k = 171 := by
  decide
