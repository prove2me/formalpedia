-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genOp_eq_op
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T02:05:45.149983+00:00
-- url     : https://prove2.me/submissions/cf361176-dea5-4914-9c17-96b7ebac756f

-- Generated from ChapterStoneTheorem.lean — solution of BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.genOp_eq_op
import Mathlib
import Definitions.Def_ChapterStoneTheorem
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_domain_le_genDomain
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_zero
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint



open scoped InnerProductSpace


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint H) (x : T.domain) :
    T.stoneGroup.genOp ⟨(x : H), T.domain_le_genDomain x.2⟩ = T.op x := T.stoneGroup.genOp_eq_of_hasDerivAt (T.hasDerivAt_stoneU_zero x)
