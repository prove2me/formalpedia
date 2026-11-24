-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_b_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:12.585344+00:00
-- url     : https://prove2.me/submissions/c19c405b-2ff3-4313-b22a-6a50e88d5e3f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_adj
import Theorems.Thm_Formalism_L2_Th1_H_ud_int

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {x x' : V} (hx : x ∈ Λ) (hx' : x' ∈ Λ) :
    bC H Ae x x' = bC H Ae x' x := by
  unfold bC
  obtain ⟨m, hm⟩ := ud_int h hx hx'
  have h1 := congrArg Complex.im (ud_adj h x x')
  rw [Complex.add_im, h.herm (Ae.symm x') x, Complex.conj_im] at h1
  have h2 : altE H (Ae.symm x) x' = altE H (Ae.symm x') x + m := by
    unfold altE
    rw [← hm]
    unfold altE
    linarith
  rw [h2, Complex.ofReal_add, mul_add, Complex.exp_add]
  have h3 : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℤ) : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  rw [h3, mul_one]
end Formalism.L2.Th1.H
