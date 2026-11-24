-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn0.phi_rad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:55.864623+00:00
-- url     : https://prove2.me/submissions/e6f952f7-26f1-4a0a-9a98-b6a270c7be15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn0_symm
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn0_mem_rad
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_symm


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
open SemicharacterExponentialLemmas
open Formalism.L2.Th1.H.IsQuadFn0
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn0
theorem _root_.solution [Fintype M] (h : IsQuadFn0 φ b) (hS : ∑ x, φ x ≠ 0) {r : M} (hr : r ∈ h.rad) :
    φ r = 1 := by
  have hb : ∀ x, b x r = 1 := fun x => (h.symm x r).trans ((h.mem_rad r).1 hr x)
  have hshift : ∑ x, φ (x + r) = ∑ x, φ x :=
    Fintype.sum_equiv (Equiv.addRight r) (fun x => φ (x + r)) φ (fun x => rfl)
  have hm : ∑ x, φ (x + r) = φ r * ∑ x, φ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [h.1, hb, mul_one, mul_comm]
  rw [hshift] at hm
  exact mul_right_cancel₀ hS (hm.symm.trans (one_mul _).symm)
end Formalism.L2.Th1.H.IsQuadFn0
