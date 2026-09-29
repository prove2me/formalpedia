-- Prove2me | solution 1 for FiniteTriangular.sum_range_75
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:20.090968+00:00
-- url     : https://prove2.me/submissions/4e91f018-3e1c-49a5-a613-03d19dd36f2d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 75, k = 2775 := by
  decide
