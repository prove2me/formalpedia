-- Prove2me | solution 1 for Formalism.L2.Th1.H.kernelTermShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:21.813944+00:00
-- url     : https://prove2.me/submissions/bbe9aebf-b2f0-43c1-8ec8-0eeb89804649

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionActionPermutesPlaces
import Theorems.Thm_Formalism_L2_Th1_H_wt_eq_cexp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : TermShift := by
  intro V _ _ H hH α δ Ae hI hA
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hI a b
  refine ⟨fun x z => ?_, fun z => ?_⟩
  · obtain ⟨v, rfl⟩ : ∃ v, x = Ae (δ v) := ⟨δ.symm (Ae.symm x), by simp⟩
    obtain ⟨y, rfl⟩ : ∃ y, z = δ y := ⟨δ.symm z, by simp⟩
    simp only [termT, phiC, gq, opU, kerK, cayC, wt_eq_cexp H hH, LinearEquiv.symm_apply_apply]
    simp only [← Complex.exp_add, mul_assoc]
    congr 2
    simp only [hA, LinearEquiv.symm_apply_apply, map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, hi, smul_eq_mul]
    ring
  · obtain ⟨y, rfl⟩ : ∃ y, z = δ y := ⟨δ.symm z, by simp⟩
    rw [gq, Complex.norm_exp]
    congr 1
    have hc : H (δ y) y = conj (H y (δ y)) := hH y (δ y)
    simp only [hA, LinearEquiv.symm_apply_apply, map_sub, LinearMap.sub_apply, hi, hc, neg_mul,
      Complex.neg_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.conj_re]
    ring
end Formalism.L2.Th1.H
