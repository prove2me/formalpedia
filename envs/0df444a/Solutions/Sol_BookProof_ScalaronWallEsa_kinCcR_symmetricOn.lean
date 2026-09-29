-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.kinCcR_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:35:43.538596+00:00
-- url     : https://prove2.me/submissions/1c34a092-0aed-4f2b-8a97-22df17f97349

-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.kinCcR_symmetricOn
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_StrichartzWave_constCoeffOp_symmetric
import Theorems.Thm_BookProof_ScalaronEsa_symmetricOn_inclusion
open BookProof.ScalaronWallEsa













open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn (ccDomain ℝ) kinCcR := symmetricOn_inclusion _ _ (constCoeffOp_symmetric _ _ _)
