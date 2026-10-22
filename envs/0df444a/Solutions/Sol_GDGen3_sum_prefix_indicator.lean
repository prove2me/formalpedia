-- Prove2me | solution 1 for GDGen3.sum_prefix_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:56:54.339004+00:00
-- url     : https://prove2.me/submissions/ac0cc02a-6b7c-4a2d-b647-701d0f9fe7dc

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (F : ℕ → ℝ) (B a : ℕ) (ha : a ≤ B) :
    (∑ k ∈ range B, if k < a then F k else 0) = ∑ k ∈ range a, F k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega
