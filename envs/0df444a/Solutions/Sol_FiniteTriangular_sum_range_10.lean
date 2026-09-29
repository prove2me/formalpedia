-- Prove2me | solution 1 for FiniteTriangular.sum_range_10
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:05.929985+00:00
-- url     : https://prove2.me/submissions/9b43e47f-aa20-4789-980c-a689ccb26040

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 10, k = 45 := by
  decide
