-- Prove2me | solution 1 for FiniteTriangular.sum_range_14
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:09.917984+00:00
-- url     : https://prove2.me/submissions/9e3aea63-f1e5-4d50-9db6-5089b2813a1b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 14, k = 91 := by
  decide
