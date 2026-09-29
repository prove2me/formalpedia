-- Prove2me | solution 1 for FiniteTriangular.sum_range_121
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:54:14.046016+00:00
-- url     : https://prove2.me/submissions/89e93a89-ffa1-4af9-9b64-465c50d97cd0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 121, k = 7260 := by
  decide
