-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T01:18:41.494487+00:00
-- url     : https://prove2.me/submissions/f9c4ec35-fdb7-4bed-b52f-22893ccdbd4e

-- Generated from ChapterStoneTheorem.lean — solution of BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.gen_stoneGroup_eq
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_ext_prime
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_genOp_eq_op
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_genDomain_eq_domain
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint



open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H]

set_option maxHeartbeats 1000000 in
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.ChapterStoneResolvent
theorem solution (T : UnboundedSelfAdjoint H) : T.stoneGroup.gen = T := by

  refine ext_prime T.genDomain_eq_domain ?_
  intro x _ hx'
  exact T.genOp_eq_op ⟨x, hx'⟩
