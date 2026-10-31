-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diagOnePart_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:17.396141+00:00
-- url     : https://prove2.me/submissions/f521ec32-e947-41c5-a7bf-dfc0c171957b

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diagOnePart_coe
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
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x : finiteModeDomain b) :
    ((diagOnePart b w x : finiteModeDomain b) : F)
      = ∑ i ∈ ((modeBasis b).repr x).support,
          (((w i : ℝ) : ℂ) * ((modeBasis b).repr x i)) • b i := by

  rw [diagOnePart, Basis.constr_apply, Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, Submodule.coe_smul, modeBasis_coe, smul_smul,
    mul_comm ((modeBasis b).repr x i) (((w i : ℝ) : ℂ))]
