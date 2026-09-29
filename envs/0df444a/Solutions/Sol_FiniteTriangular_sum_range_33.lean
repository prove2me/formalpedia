-- Prove2me | solution 1 for FiniteTriangular.sum_range_33
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:13:18.977743+00:00
-- url     : https://prove2.me/submissions/d28d965b-6fb8-4a95-ba0f-ec5be448999e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 33, k = 528 := by
  decide
