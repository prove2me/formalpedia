-- Prove2me | solution 1 for FiniteTriangular.sum_range_45
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:20.472127+00:00
-- url     : https://prove2.me/submissions/d90a8865-0b3b-42c8-bb35-6810c9412338

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 45, k = 990 := by
  decide
