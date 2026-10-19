-- Prove2me | solution 1 for BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:30.539978+00:00
-- url     : https://prove2.me/submissions/92053217-4bc5-423e-8e1a-54977b7c58b3

-- Generated from ChapterYangMillsFockGapChain.lean — solution of BookProof.YangMillsFockGapChain.isPosCol_shiftCol_opCol_of_form_gap
import Mathlib
import Definitions.Def_ChapterYangMillsFockGapChain
import Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_opCol
import Theorems.Thm_BookProof_FockSecondQuantization_isPosCol_opCol
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.YangMillsFockGapChain



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability
open BookProof.FockFieldPerturbation
open BookProof.FarisLavine BookProof.HermiteGalerkin
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.BandEnclosure
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ}
    (hgap : ∀ x : finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    IsPosCol (shiftCol (opCol b A) mu) := by

  have hpos : ∀ x : finiteModeDomain b,
      0 ≤ quadForm ((finiteModeDomain b).subtype.comp
        (A - ((mu : ℝ) : ℂ) • LinearMap.id)) x := by
    intro x
    have hval : quadForm ((finiteModeDomain b).subtype.comp
        (A - ((mu : ℝ) : ℂ) • LinearMap.id)) x
        = quadForm ((finiteModeDomain b).subtype.comp A) x - mu * ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_sub,
        Submodule.coe_smul, inner_sub_right, inner_smul_right, Complex.sub_re,
        Complex.re_ofReal_mul, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [hval]
    linarith [hgap x]
  rw [shiftCol_opCol]
  exact isPosCol_opCol hpos
