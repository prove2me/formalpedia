-- Prove2me | solution 1 for FiniteTriangular.sum_range_1082
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:25.909704+00:00
-- url     : https://prove2.me/submissions/0871bb15-21c5-456f-b10f-69fafb334c52

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1082, k = 584821 := by
  rw [sum_range_id]
