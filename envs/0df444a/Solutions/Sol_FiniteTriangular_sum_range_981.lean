-- Prove2me | solution 1 for FiniteTriangular.sum_range_981
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:12.485838+00:00
-- url     : https://prove2.me/submissions/933f7695-37f6-4b89-93ba-ab1bbbe2b8bd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 981, k = 480690 := by
  rw [sum_range_id]
