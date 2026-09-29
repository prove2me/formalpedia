-- Prove2me | solution 1 for FiniteTriangular.sum_range_9
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:01:10.248211+00:00
-- url     : https://prove2.me/submissions/799e2760-379d-4662-a0b7-e7ca1958218d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 9, k = 36 := by
  decide
