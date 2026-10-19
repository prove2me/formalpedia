-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:04:10.750254+00:00
-- url     : https://prove2.me/submissions/f1c9ee50-316e-408f-b0be-116598378764

import Mathlib
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
-- Generated from ChapterStoneUnitary.lean — theorem BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.stoneU_surjective
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent


open scoped InnerProductSpace
open Filter Topology NormedSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



variable (T : UnboundedSelfAdjoint H)


theorem solution (t : ℝ) : Function.Surjective (T.stoneU t) := by
  intro y
  refine ⟨T.stoneU (-t) y, ?_⟩
  rw [T.stoneU_apply_stoneU, add_neg_cancel, T.stoneU_zero]
  rfl

