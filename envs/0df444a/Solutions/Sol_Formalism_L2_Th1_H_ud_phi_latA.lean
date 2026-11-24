-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_phi_latA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:27:33.698249+00:00
-- url     : https://prove2.me/submissions/296b6832-7532-4442-86c3-89a0a6ebcc62

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic

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
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) {w : V} (hw : w ∈ Λ) (hy : δ w ∈ Λ) :
    phiC H α Ae (Ae (δ w)) = 1 := by
  have hyd : Ae (δ w) = δ w - w := by rw [h.cay, LinearEquiv.symm_apply_apply]
  have hyΛ : δ w - w ∈ Λ := Λ.sub_mem hy hw
  have h0 : (H w w).im = 0 := by
    have hh := congrArg Complex.im (h.herm w w)
    simp only [Complex.conj_im] at hh
    linarith
  have hcy : cayC Ae (Ae (δ w)) = (1 / 2 : ℂ) • (δ w + w) := by
    rw [cayC, LinearEquiv.symm_apply_apply, hyd]
    module
  have hH : H (cayC Ae (Ae (δ w))) (Ae (δ w)) = Complex.I * (altE H w (δ w) : ℂ) := by
    rw [hcy, hyd]
    simp only [map_smul, map_add, map_sub, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    have i1 : H (δ w) (δ w) = H w w := h.isom w w
    have i2 : H (δ w) w = (starRingEnd ℂ) (H w (δ w)) := h.herm w (δ w)
    rw [i1, i2]
    have hs := Complex.sub_conj (H w (δ w))
    push_cast at hs
    unfold altE
    linear_combination (1 / 2 : ℂ) * hs
  have hαy : α (Ae (δ w)) = Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)) := by
    have e1 := h.semi.2 _ hyΛ w hw
    rw [sub_add_cancel, h.inv w hw] at e1
    have hE : altE H (δ w - w) w = -altE H w (δ w) := by
      have i2 := congrArg Complex.im (h.herm w (δ w))
      simp only [altE, map_sub, LinearMap.sub_apply, Complex.sub_im, h0, sub_zero]
      simp only [Complex.conj_im] at i2
      exact i2
    rw [hE] at e1
    have hα : α w ^ 2 = 1 := by
      rcases h.semi.1 w hw with h' | h' <;> rw [h'] <;> norm_num
    have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE H w (δ w) : ℝ) : ℂ)) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      push_cast
      ring
    rw [hyd]
    linear_combination (-(α w * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)))) * e1 +
      (Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H w (δ w) : ℂ)) - α (δ w - w)) * hα -
      (α (δ w - w) * α w ^ 2) * hexp
  unfold phiC
  rw [hαy, hH, ← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  ring
end Formalism.L2.Th1.H
