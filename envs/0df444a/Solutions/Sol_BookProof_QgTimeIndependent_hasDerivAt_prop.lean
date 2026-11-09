-- Prove2me | solution 1 for BookProof.QgTimeIndependent.hasDerivAt_prop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:57:12.64192+00:00
-- url     : https://prove2.me/submissions/493310e2-6767-4925-a3d8-615ad66be857

-- Generated from ChapterQgTimeIndependentFlow.lean — solution of BookProof.QgTimeIndependent.hasDerivAt_prop
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_hasDerivAt_stoneU_op
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.QgTimeIndependent




open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint E) (x : T.domain) (t s : ℝ) :
    HasDerivAt (fun r : ℝ => prop T r s (x : E))
      ((-Complex.I) • T.op ⟨T.stoneU (t - s) (x : E), T.stoneU_mem_domain (t - s) x⟩) t := by

  have h := T.hasDerivAt_stoneU_op x (t - s)
  exact h.comp_sub_const t s
