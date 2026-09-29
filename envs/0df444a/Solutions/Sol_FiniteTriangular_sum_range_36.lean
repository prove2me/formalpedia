-- Prove2me | solution 1 for FiniteTriangular.sum_range_36
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:15:11.976985+00:00
-- url     : https://prove2.me/submissions/16a2780a-9372-4bc1-93a9-7afb25fb0117

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 36, k = 630 := by
  decide
