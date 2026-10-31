-- Prove2me | solution 1 for BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-30T22:47:40.746809+00:00
-- url     : https://prove2.me/submissions/6343c62c-7327-49ea-91f7-25f2feea915f

-- Generated from ChapterFockDiagonalGapChain.lean — solution of BookProof.FockDiagonalGapChain.diag_isPosCol_shiftCol
import Mathlib
import Definitions.Def_ChapterFockDiagonalGapChain
import Theorems.Thm_BookProof_FockDiagonalGapChain_diagOnePart_quadForm_ge
import Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_isPosCol_opCol
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
import Definitions.Def_ChapterFockSecondQuantization
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
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (w : ℕ → ℝ) {m : ℝ}
    (hw : ∀ k, m ≤ w k) :
    IsPosCol (shiftCol (opCol b (diagOnePart b w)) m) := by

  have hpos : ∀ x : finiteModeDomain b,
      0 ≤ quadForm ((finiteModeDomain b).subtype.comp
        (diagOnePart b w - ((m : ℝ) : ℂ) • LinearMap.id)) x := by
    intro x
    have hval : quadForm ((finiteModeDomain b).subtype.comp
        (diagOnePart b w - ((m : ℝ) : ℂ) • LinearMap.id)) x
        = quadForm ((finiteModeDomain b).subtype.comp (diagOnePart b w)) x
          - m * ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_sub,
        Submodule.coe_smul, inner_sub_right, inner_smul_right, Complex.sub_re,
        Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]
      norm_cast
    have := diagOnePart_quadForm_ge b w hw x
    rw [hval]
    linarith
  rw [shiftCol_opCol]
  exact isPosCol_opCol hpos
