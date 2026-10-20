-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.domain_le_genDomain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:22:38.061553+00:00
-- url     : https://prove2.me/submissions/e60c1059-e07a-4287-97b1-0190b47099dd

-- Generated from ChapterStoneTheorem.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.domain_le_genDomain
import Mathlib
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_zero
import Definitions.Def_ChapterStoneTheorem
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint in
theorem solution (T : UnboundedSelfAdjoint H) :
    T.domain ≤ T.stoneGroup.genDomain := by 
  intro x hx
  exact (BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.hasDerivAt_stoneU_zero T ⟨x, hx⟩).differentiableAt
