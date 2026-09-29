-- Prove2me | solution 1 for FiniteTriangular.sum_range_129
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:25.492292+00:00
-- url     : https://prove2.me/submissions/7fa27a1f-6575-4bcc-82aa-09e86328f39f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 129, k = 8256 := by
  rw [sum_range_id]
