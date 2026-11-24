-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:41:40.069775+00:00
-- url     : https://prove2.me/submissions/0a980b2a-9e95-42c7-99a0-858658f49c05

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_isom_symm

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
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) (x y : V) :
    H (Ae.symm x) y + H x (Ae.symm y) = H x y := by
  obtain ⟨a, rfl⟩ : ∃ a, Ae a = x := ⟨Ae.symm x, Ae.apply_symm_apply x⟩
  obtain ⟨b, rfl⟩ : ∃ b, Ae b = y := ⟨Ae.symm y, Ae.apply_symm_apply y⟩
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  simp only [h.cay, map_sub, LinearMap.sub_apply, ud_isom_symm h]
  ring
end Formalism.L2.Th1.H
