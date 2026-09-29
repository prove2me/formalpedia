-- Prove2me | solution 1 for FiniteTriangular.sum_range_107
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:24.118367+00:00
-- url     : https://prove2.me/submissions/ada16d26-a43e-41b4-a5d7-087153d60b84

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 107, k = 5671 := by
  decide
