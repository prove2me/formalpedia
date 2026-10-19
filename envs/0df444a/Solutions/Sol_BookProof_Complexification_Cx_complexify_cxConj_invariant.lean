-- Prove2me | solution 1 for BookProof.Complexification.Cx.complexify_cxConj_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:51:20.650929+00:00
-- url     : https://prove2.me/submissions/0fc9296a-a46f-464d-bedf-317cca5f6482

import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.complexify_cxConj_invariant
open BookProof.Complexification
open BookProof.Complexification.Cx


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


theorem solution (Y : Submodule ℝ W) :
    ∀ x ∈ complexify Y, cxConj x ∈ complexify Y := by
  intro x hx
  simp only [mem_complexify, Cx.cxConj_apply] at hx ⊢
  exact ⟨hx.1, Y.neg_mem hx.2⟩

