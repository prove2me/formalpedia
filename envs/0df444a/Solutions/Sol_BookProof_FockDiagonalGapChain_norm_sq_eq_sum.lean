-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.norm_sq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:25.064859+00:00
-- url     : https://prove2.me/submissions/d44a22f9-d420-49f6-b010-cd47c9b97bee

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.norm_sq_eq_sum
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_conj_mul_ofReal
import Theorems.Thm_BookProof_FockDiagonalGapChain_inner_self_ofReal
import Theorems.Thm_BookProof_FockDiagonalGapChain_coe_eq_linearCombination
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
    ‖(x : F)‖ ^ 2 = ∑ i ∈ ((modeBasis b).repr x).support, ‖(modeBasis b).repr x i‖ ^ 2 := by

  have h : ((‖(x : F)‖ ^ 2 : ℝ) : ℂ)
      = ((∑ i ∈ ((modeBasis b).repr x).support, ‖(modeBasis b).repr x i‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : (inner ℂ (x : F) (x : F) : ℂ) = ((‖(x : F)‖ ^ 2 : ℝ) : ℂ) :=
      inner_self_ofReal (x : F)
    rw [← h1, coe_eq_linearCombination b x, b.orthonormal.inner_finsupp_eq_sum_left]
    simp only [Finsupp.sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conj_mul_ofReal]
    push_cast
    ring
  exact_mod_cast h
