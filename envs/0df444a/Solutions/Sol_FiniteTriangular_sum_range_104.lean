-- Prove2me | solution 1 for FiniteTriangular.sum_range_104
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:39.775425+00:00
-- url     : https://prove2.me/submissions/a2edf82e-b314-48ae-9faf-94bea7ace39f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 104, k = 5356 := by
  decide
