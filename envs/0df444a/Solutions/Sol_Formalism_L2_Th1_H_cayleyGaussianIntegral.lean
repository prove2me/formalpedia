-- Prove2me | solution 1 for Formalism.L2.Th1.H.cayleyGaussianIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:41.576028+00:00
-- url     : https://prove2.me/submissions/9200702d-6100-4224-86fa-71d3f9321ad6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral
import Theorems.Thm_Formalism_L2_Th1_H_gauss_pi
import Theorems.Thm_Formalism_L2_Th1_H_haar_transfer
import Theorems.Thm_Formalism_L2_Th1_H_det_of_diag
import Theorems.Thm_Formalism_L2_Th1_H_form_of_diag
import Theorems.Thm_Formalism_L2_Th1_H_unitary_diag


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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : GaussQuad := by
  intro V _ _ _ _ _ μ _ H hH hP δ Ae hδ hAe
  classical
  obtain ⟨b, l, hb, hbl, hl⟩ := unitary_diag H hH hP δ Ae hδ hAe
  obtain ⟨κ, hκ⟩ := haar_transfer μ b.equivFun.symm
  have hq : (fun w => gq H Ae (b.equivFun.symm w)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b l (Ae : V →ₗ[ℂ] V) hb hbl w
    simp only [LinearEquiv.coe_coe] at h1
    unfold gq
    rw [h1]
  have hw : (fun w => ((wt H (b.equivFun.symm w) : ℝ) : ℂ)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b (fun _ => (1 : ℂ)) LinearMap.id hb (fun i => by simp) w
    simp only [LinearMap.id_apply] at h1
    have hs : (∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp
    unfold wt
    rw [h1, hs, Complex.ofReal_re, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  have hgq := gauss_pi l hl
  have hgw := gauss_pi (n := Fin (Module.finrank ℂ V)) (fun _ => (1 : ℂ)) (fun _ => by simp)
  rw [← hq] at hgq
  rw [← hw] at hgw
  refine ⟨(hκ _).1 hgq.1, ?_⟩
  rw [(hκ (gq H Ae)).2, hgq.2, ← integral_complex_ofReal, (hκ (fun z => ((wt H z : ℝ) : ℂ))).2, hgw.2,
    det_of_diag b l (Ae : V →ₗ[ℂ] V) hbl]
  simp [div_eq_mul_inv]
end Formalism.L2.Th1.H
