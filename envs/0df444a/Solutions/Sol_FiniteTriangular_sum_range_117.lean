-- Prove2me | solution 1 for FiniteTriangular.sum_range_117
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:20.569247+00:00
-- url     : https://prove2.me/submissions/7da8a4e8-1b2a-47cf-939a-6a4cfcd0bbd8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 117, k = 6786 := by
  decide
