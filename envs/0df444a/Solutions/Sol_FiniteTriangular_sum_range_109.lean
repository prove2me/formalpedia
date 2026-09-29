-- Prove2me | solution 1 for FiniteTriangular.sum_range_109
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:25.867541+00:00
-- url     : https://prove2.me/submissions/352e2822-752f-4528-bd6c-2634c18af240

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 109, k = 5886 := by
  decide
