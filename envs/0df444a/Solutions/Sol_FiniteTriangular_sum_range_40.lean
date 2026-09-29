-- Prove2me | solution 1 for FiniteTriangular.sum_range_40
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:16.415988+00:00
-- url     : https://prove2.me/submissions/7211899b-efad-4d93-a35b-7ad918fa419f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 40, k = 780 := by
  decide
