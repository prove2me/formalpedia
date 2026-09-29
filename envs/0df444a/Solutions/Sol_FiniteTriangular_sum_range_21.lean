-- Prove2me | solution 1 for FiniteTriangular.sum_range_21
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:36.974223+00:00
-- url     : https://prove2.me/submissions/c3aad71c-9dae-40da-99f7-94946a2c5c9f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 21, k = 210 := by
  decide
