-- Prove2me | solution 1 for BookProof.QgTimeIndependent.isSchrodingerSolution_prop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:57:31.848459+00:00
-- url     : https://prove2.me/submissions/02e961f5-012d-4a41-ad84-3f20f0479e2e

-- Generated from ChapterQgTimeIndependentFlow.lean — solution of BookProof.QgTimeIndependent.isSchrodingerSolution_prop
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Theorems.Thm_BookProof_QgTimeIndependent_hasDerivAt_prop
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
theorem solution (T : UnboundedSelfAdjoint E) (s : ℝ) (x : T.domain) :
    IsSchrodingerSolution T (fun r : ℝ => prop T r s (x : E)) := by

  refine ⟨fun r => T.stoneU_mem_domain (r - s) x, fun r => ?_⟩
  have h := hasDerivAt_prop T x r s
  exact h
