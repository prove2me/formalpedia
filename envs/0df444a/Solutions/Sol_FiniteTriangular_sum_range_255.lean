-- Prove2me | solution 1 for FiniteTriangular.sum_range_255
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:18.138138+00:00
-- url     : https://prove2.me/submissions/ad7d04aa-a9af-4d46-8811-52822a4542dc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 255, k = 32385 := by
  rw [sum_range_id]
