-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_phi_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:14:42.046413+00:00
-- url     : https://prove2.me/submissions/8df500df-c241-4b40-8653-2d907a2f59d2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_phi_add
import Theorems.Thm_Formalism_L2_Th1_H_ud_b_symm
import Theorems.Thm_Formalism_L2_Th1_H_mem_latA
import Theorems.Thm_Formalism_L2_Th1_H_ud_latA_le
import Theorems.Thm_Formalism_L2_Th1_H_ud_radical_of_mem
import Theorems.Thm_Formalism_L2_Th1_H_ud_phi_latA

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x y : V} (hx : x ∈ Λ) (hy : y ∈ latA Λ δ Ae) :
    phiC H α Ae (x + y) = phiC H α Ae x := by
  have hyΛ := ud_latA_le h hy
  rw [ud_phi_add h hx hyΛ, ud_b_symm h hx hyΛ, ud_radical_of_mem h hy hx]
  obtain ⟨w, hw, hδ, rfl⟩ := mem_latA.mp hy
  rw [ud_phi_latA h hw hδ, mul_one, mul_one]
end Formalism.L2.Th1.H
