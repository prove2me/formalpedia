-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_phi_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:10.156533+00:00
-- url     : https://prove2.me/submissions/a9070803-9e31-4af0-a34f-c92a3d6f9309

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_skew
import Theorems.Thm_Formalism_L2_Th1_H_ud_int
import Theorems.Thm_Formalism_L2_Th1_H_altE_cayC
import Theorems.Thm_Formalism_L2_Th1_H_cayC_add
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_herm_sub_swap
import Theorems.Thm_Formalism_L2_Th1_H_herm_sub_swap


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
    phiC H α Ae (x + x') = phiC H α Ae x * phiC H α Ae x' * bC H Ae x x' := by
  obtain ⟨m, hm⟩ := ud_int h hx hx'
  have h1 : H (cayC Ae x') x = -conj (H (cayC Ae x) x') := by
    rw [ud_skew h x' x, h.herm (cayC Ae x) x']
  have h2 : H (cayC Ae x) x' - conj (H (cayC Ae x) x')
      = 2 * Complex.I * (altE H (cayC Ae x) x' : ℂ) := by
    rw [← h.herm (cayC Ae x) x']
    exact herm_sub_swap H h.herm _ _
  have h3 : (altE H (cayC Ae x) x' : ℂ)
      = (altE H (Ae.symm x) x' : ℂ) - (altE H x x' : ℂ) / 2 := by
    rw [altE_cayC]; push_cast; rfl
  have h4 : (altE H x x' : ℂ) = (m : ℂ) := by rw [hm]; push_cast; rfl
  have key : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x x' : ℂ))
        * Complex.exp (-(Real.pi : ℂ) * H (cayC Ae (x + x')) (x + x'))
      = Complex.exp (-(Real.pi : ℂ) * H (cayC Ae x) x) * Complex.exp (-(Real.pi : ℂ) * H (cayC Ae x') x')
        * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (Ae.symm x) x' : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [cayC_add, map_add, LinearMap.add_apply]
    linear_combination (-(Real.pi : ℂ)) * h1 + (-(Real.pi : ℂ)) * h2
      + (-(2 * (Real.pi : ℂ) * Complex.I)) * h3 + (2 * (Real.pi : ℂ) * Complex.I) * h4
  simp only [phiC, bC]
  rw [h.semi.2 x hx x' hx']
  linear_combination (α x * α x') * key
end Formalism.L2.Th1.H
