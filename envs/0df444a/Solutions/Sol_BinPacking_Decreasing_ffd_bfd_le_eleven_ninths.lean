-- Prove2me | solution 1 for BinPacking.Decreasing.ffd_bfd_le_eleven_ninths
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T03:55:58.545315+00:00
-- url     : https://prove2.me/submissions/a862f436-3e2b-4203-ba43-686e456c31d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model
import Theorems.Thm_BinPacking_Decreasing_delete_small_items
import Theorems.Thm_BinPacking_Decreasing_ffd_le_eleven_ninths_large_items
import Theorems.Thm_BinPacking_Decreasing_bfd_le_ffd

set_option autoImplicit false

open BinPacking.Decreasing in
theorem solution (L : List ℝ) (hL : IsList L) :
    (FFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 ∧
      (BFD L : ℝ) ≤ (11 / 9 : ℝ) * (optBins L : ℝ) + 4 := by
  have hc : ((11 : ℝ) / 9 - 1) / (11 / 9) = 2 / 11 := by norm_num
  have hdel := delete_small_items L hL (11 / 9) 4 (by norm_num) (by norm_num)
  rw [hc] at hdel
  have hL'list : IsList (L.filter (fun a => decide ((2 / 11 : ℝ) < a))) :=
    fun a ha => hL a (List.mem_of_mem_filter ha)
  have hbig : ∀ a ∈ L.filter (fun a => decide ((2 / 11 : ℝ) < a)), (2 / 11 : ℝ) < a :=
    fun a ha => by simpa using (List.mem_filter.1 ha).2
  have h6 : ∀ a ∈ L.filter (fun a => decide ((2 / 11 : ℝ) < a)), (1 / 6 : ℝ) ≤ a :=
    fun a ha => by linarith [hbig a ha]
  have hF := ffd_le_eleven_ninths_large_items _ hL'list hbig
  have hB : (BFD (L.filter (fun a => decide ((2 / 11 : ℝ) < a))) : ℝ) ≤
      FFD (L.filter (fun a => decide ((2 / 11 : ℝ) < a))) := by
    exact_mod_cast bfd_le_ffd _ hL'list h6
  constructor
  · by_contra h
    push_neg at h
    exact absurd (hdel.1 h) (not_lt.2 hF)
  · by_contra h
    push_neg at h
    exact absurd (hdel.2 h) (not_lt.2 (hB.trans hF))
