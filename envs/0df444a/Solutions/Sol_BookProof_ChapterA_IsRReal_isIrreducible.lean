-- Prove2me | solution 1 for BookProof.ChapterA.IsRReal.isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:30:05.164019+00:00
-- url     : https://prove2.me/submissions/2740bd47-42b1-4efc-95f2-6371edfbc163

import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
import Theorems.Thm_BookProof_Complexification_irreducible_iff_no_conj_subsystem
-- Generated from ChapterA1c.lean — theorem BookProof.ChapterA.IsRReal.isIrreducible
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]


theorem solution {M : System ℝ W} (h : IsRReal M) :
    M.IsIrreducible := by
  rw [BookProof.Complexification.irreducible_iff_no_conj_subsystem]
  intro X hX _
  exact h X hX

