-- Prove2me | solution 1 for FiniteTriangular.sum_range_480
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:15:40.027717+00:00
-- url     : https://prove2.me/submissions/4617ae81-fb7c-4f3d-bd37-de1a821f9931

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 480, k = 114960 := by
  rw [sum_range_id]
