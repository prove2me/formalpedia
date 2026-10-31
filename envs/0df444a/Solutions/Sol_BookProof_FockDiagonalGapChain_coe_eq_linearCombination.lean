-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.coe_eq_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:13.7264+00:00
-- url     : https://prove2.me/submissions/999e39f5-c574-48e4-8802-09b3a2e03504

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.coe_eq_linearCombination
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
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterScalaronFockGapChain
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockDiagonalGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicQuarticStability BookProof.FockCubicUnbounded
open BookProof.FockInteractionStability
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
open BookProof.HermiteCore BookProof.ScalaronFockGapChain
open Module
open BookProof.HermiteGalerkin


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (x : finiteModeDomain b) :
    (x : F) = Finsupp.linearCombination ℂ (⇑b) ((modeBasis b).repr x) := by

  calc (x : F)
      = ((Finsupp.linearCombination ℂ (⇑(modeBasis b)) ((modeBasis b).repr x) :
          finiteModeDomain b) : F) := by
        rw [(modeBasis b).linearCombination_repr x]
    _ = Finsupp.linearCombination ℂ (⇑b) ((modeBasis b).repr x) := by
        simp only [Finsupp.linearCombination_apply, Finsupp.sum,
          AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, modeBasis_coe]
