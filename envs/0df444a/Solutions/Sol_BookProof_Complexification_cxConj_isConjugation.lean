-- Prove2me | solution 1 for BookProof.Complexification.cxConj_isConjugation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:53:57.110789+00:00
-- url     : https://prove2.me/submissions/74376152-5cc3-4499-8c6c-a7f9938346d9

import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
-- Generated from Complexification.lean — theorem BookProof.Complexification.cxConj_isConjugation
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA.AntiUnitary
open BookProof.Complexification


open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


theorem solution [CompleteSpace W] (M : System ℝ W) :
    IsConjugation (cxSystem M) Cx.cxConj := by
  refine ⟨fun x => by ext <;> simp, ?_⟩
  rintro m ⟨m', hm', rfl⟩ x
  ext <;> simp [map_neg]

