-- Prove2me | solution 1 for FiniteTriangular.sum_range_53
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:13.562516+00:00
-- url     : https://prove2.me/submissions/ad719533-0fdd-4e8c-96f1-677d76d93d9f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 53, k = 1378 := by
  decide
