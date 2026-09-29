-- Prove2me | solution 1 for FiniteTriangular.sum_range_372
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:16.96789+00:00
-- url     : https://prove2.me/submissions/bb4d9438-fdcd-47ac-8d8e-ef62da80c3fb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 372, k = 69006 := by
  rw [sum_range_id]
