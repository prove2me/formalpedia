-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_radical_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:50.766349+00:00
-- url     : https://prove2.me/submissions/fa6f5013-b1ab-413f-8b7a-ce4df20b49d6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_int
import Theorems.Thm_Formalism_L2_Th1_H_mem_latA

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ latA Λ δ Ae) {x' : V}
    (hx' : x' ∈ Λ) : bC H Ae x x' = 1 := by
  obtain ⟨w, hw, hδ, rfl⟩ := mem_latA.mp hx
  obtain ⟨m, hm⟩ := ud_int h hδ hx'
  unfold bC
  rw [LinearEquiv.symm_apply_apply, hm, Complex.exp_eq_one_iff]
  exact ⟨-m, by push_cast; ring⟩
end Formalism.L2.Th1.H
