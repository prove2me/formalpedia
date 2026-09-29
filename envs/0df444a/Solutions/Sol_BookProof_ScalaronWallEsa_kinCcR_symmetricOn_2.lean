-- Prove2me | solution 2 for BookProof.ScalaronWallEsa.kinCcR_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-20T10:55:45.608331+00:00
-- url     : https://prove2.me/submissions/068aff6b-4f08-42d7-93ed-fee61a0839dd

-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.kinCcR_symmetricOn
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_ScalaronEsa_symmetricOn_inclusion
import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_symmetric
open BookProof.ScalaronWallEsa




open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (ccDomain ℝ) kinCcR := symmetricOn_inclusion _ _ (constCoeffOp_symmetric _ _ _)
