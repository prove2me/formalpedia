-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diagOnePart_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:21.104616+00:00
-- url     : https://prove2.me/submissions/bc8fb0aa-2cda-481f-af5b-6f44e7c7ac57

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diagOnePart_inner
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_coe_eq_linearCombination
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_coe
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
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) (x y : finiteModeDomain b) :
    (inner ℂ (x : F) ((diagOnePart b w y : finiteModeDomain b) : F) : ℂ)
      = ∑ i ∈ ((modeBasis b).repr y).support,
          ((w i : ℝ) : ℂ) * (starRingEnd ℂ ((modeBasis b).repr x i)) *
            ((modeBasis b).repr y i) := by

  rw [diagOnePart_coe, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, coe_eq_linearCombination b x, b.orthonormal.inner_left_finsupp]
  ring
