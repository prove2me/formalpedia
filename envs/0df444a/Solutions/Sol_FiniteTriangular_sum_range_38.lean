-- Prove2me | solution 1 for FiniteTriangular.sum_range_38
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:14.393261+00:00
-- url     : https://prove2.me/submissions/7fd0cbb0-2b34-48dc-b22f-057e0b1053b3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 38, k = 703 := by
  decide
