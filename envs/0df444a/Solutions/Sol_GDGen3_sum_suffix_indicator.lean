-- Prove2me | solution 1 for GDGen3.sum_suffix_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:57:09.973444+00:00
-- url     : https://prove2.me/submissions/26cbdc0c-d492-4da0-9b68-00a9127263cf

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (F : ℕ → ℝ) (N a : ℕ) :
    (∑ k ∈ range (N + 1), if a < k then F k else 0) = ∑ k ∈ Icc (a + 1) N, F k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Icc]
  omega
