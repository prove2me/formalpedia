-- Prove2me | solution 1 for Formalism.L2.Th1.H.cayleyDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:12:11.07641+00:00
-- url     : https://prove2.me/submissions/3c7ae2f7-56b7-4c77-85a9-3cb4a5c100f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_UnitaryEighthOf
import Theorems.Thm_Formalism_L2_Th1_H_Cay_det_adj

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
theorem _root_.solution : DetCayley := by
  intro V _ _ _ H hH hpos δ Ae hI hA
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hI a b
  have hadj : ∀ x y, H ((Ae : V →ₗ[ℂ] V) x) y = H x (((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) y) := by
    intro x y
    obtain ⟨x, rfl⟩ : ∃ x', x = δ x' := ⟨δ.symm x, by simp⟩
    simp only [LinearEquiv.coe_coe, hA, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, hi]
  have h1 := Cay.det_adj H hpos _ _ hadj
  have h2 : ((LinearMap.id : V →ₗ[ℂ] V) - (δ : V →ₗ[ℂ] V)) = ((-1 : ℂ) • (δ : V →ₗ[ℂ] V)) ∘ₗ (Ae : V →ₗ[ℂ] V) := by
    ext x
    simp [hA]
  conv_lhs => rw [h1, Complex.conj_conj, h2, LinearMap.det_comp, LinearMap.det_smul]
end Formalism.L2.Th1.H
