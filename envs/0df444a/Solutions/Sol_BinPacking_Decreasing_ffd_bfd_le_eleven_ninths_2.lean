-- Prove2me | solution 2 for BinPacking.Decreasing.ffd_bfd_le_eleven_ninths
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T11:57:57.4514+00:00
-- url     : https://prove2.me/submissions/40edcbc1-4ad1-4dcb-acca-c92e32a83e43
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model
import Theorems.Thm_BinPacking_Decreasing_delete_small_items
import Theorems.Thm_BinPacking_Decreasing_bfd_le_ffd
import Theorems.Thm_BinPacking_Decreasing_ffd_le_eleven_ninths_large_items

open BinPacking.Decreasing

theorem solution (L : List ℝ) (hL : IsList L) :
    (FFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 ∧
      (BFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 := by
  have hdel := delete_small_items L hL (11 / 9) 4 (by norm_num) (by norm_num)
  set L' := L.filter (fun a => decide (((11 / 9 : ℝ) - 1) / (11 / 9) < a))
  have hL' : IsList L' := by
    intro a ha
    exact hL a (List.mem_of_mem_filter ha)
  have h211 : ∀ a ∈ L', (2 / 11 : ℝ) < a := by
    intro a ha
    have h1 : decide (((11 / 9 : ℝ) - 1) / (11 / 9) < a) = true := (List.mem_filter.mp ha).2
    have h2 : ((11 / 9 : ℝ) - 1) / (11 / 9) < a := of_decide_eq_true h1
    linarith
  have h6 : ∀ a ∈ L', (1 / 6 : ℝ) ≤ a := by
    intro a ha
    have := h211 a ha
    linarith
  have hFFD' : (FFD L' : ℝ) ≤ (11 / 9 : ℝ) * (optBins L' : ℝ) + 4 :=
    ffd_le_eleven_ninths_large_items L' hL' h211
  have hBFD_le_FFD' : (BFD L' : ℝ) ≤ (FFD L' : ℝ) := by
    exact_mod_cast bfd_le_ffd L' hL' h6
  constructor
  · by_contra! h
    have := hdel.1 h
    linarith
  · by_contra! h
    have := hdel.2 h
    linarith
