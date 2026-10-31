-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.freeDispersion_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:56.96849+00:00
-- url     : https://prove2.me/submissions/1f9ec3b6-38db-4cb8-8d1e-2bcb119c7dd9

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.freeDispersion_ge
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
open BookProof.FockDiagonalGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore BookProof.ScalaronFockGapChain
open Module


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℝ} (hm : 0 ≤ m) (p : ℕ → ℝ) (k : ℕ) :
    m ≤ freeDispersion m p k := by

  have h : m ^ 2 ≤ (p k) ^ 2 + m ^ 2 := by nlinarith [sq_nonneg (p k)]
  calc m = Real.sqrt (m ^ 2) := (Real.sqrt_sq hm).symm
    _ ≤ Real.sqrt ((p k) ^ 2 + m ^ 2) := Real.sqrt_le_sqrt h
