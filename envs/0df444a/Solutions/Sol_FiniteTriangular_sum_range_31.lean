-- Prove2me | solution 1 for FiniteTriangular.sum_range_31
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:17.571216+00:00
-- url     : https://prove2.me/submissions/ac0c67d0-01fb-4a85-95fa-4e2d819f58c5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 31, k = 465 := by
  decide
