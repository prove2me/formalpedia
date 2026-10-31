-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:33.021641+00:00
-- url     : https://prove2.me/submissions/7e42f858-6ff7-49bb-a78c-ea96ac5afa02

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diagOnePart_quadForm_ge
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_conj_mul_ofReal
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_inner
import Theorems.Thm_BookProof_FockDiagonalGapChain_norm_sq_eq_sum
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
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
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
open BookProof.HermiteProductCore


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hw : ∀ k, m ≤ w k) (x : finiteModeDomain b) :
    m * ‖(x : F)‖ ^ 2
      ≤ quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x := by

  classical
  have hform : quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
      = ∑ i ∈ ((modeBasis b).repr x).support, w i * ‖(modeBasis b).repr x i‖ ^ 2 := by
    have h : (inner ℂ (x : F) ((diagOnePart b w x : finiteModeDomain b) : F) : ℂ)
        = ((∑ i ∈ ((modeBasis b).repr x).support,
            w i * ‖(modeBasis b).repr x i‖ ^ 2 : ℝ) : ℂ) := by
      rw [diagOnePart_inner b w x x]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, conj_mul_ofReal]
      push_cast
      ring
    have hq : quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
        = (inner ℂ (x : F) ((diagOnePart b w x : finiteModeDomain b) : F) : ℂ).re := rfl
    rw [hq, h, Complex.ofReal_re]
  rw [hform, norm_sq_eq_sum b x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
