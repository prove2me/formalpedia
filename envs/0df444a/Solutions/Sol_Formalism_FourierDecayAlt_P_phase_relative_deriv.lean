-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_relative_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:53.126629+00:00
-- url     : https://prove2.me/submissions/c809526a-128a-4975-93aa-e26fecd49cb3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_phase_function_eq_sum_add_prod_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_lin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_contDiffAt_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_contDiff_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_cst_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_prod_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_fderiv_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_fderiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.PhaseFunctionRelativeDeriv := by
  intro m
  refine ⟨fun D' x hx => ⟨?_, ?_⟩, fun j hj => ⟨a_cst (m + 1) (j + 1), fun D' x r hr hxr => ?_⟩⟩
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    rw [← a_fderiv_single D' x hx k]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [Pi.norm_single]
    simp
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [a_fderiv_apply D' x hx]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖v k * dg0 D' x k‖ ≤ ∑ _k : Fin (m + 1), ‖v‖ * ‖dg0 D' x‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm v k) (norm_le_pi_norm _ k) (norm_nonneg _) (norm_nonneg _)
      _ = ((m : ℝ) + 1) * ‖dg0 D' x‖ * ‖v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  · have hx : ∀ k, x k ≠ 0 := fun k h => by
      have := hxr k
      rw [h, norm_zero] at this
      linarith
    obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image (univ : Finset (Fin (m + 1))) (fun k => ‖x k‖)
      ⟨0, Finset.mem_univ _⟩
    have hpos : ∀ k, 0 < ‖x k‖ := fun k => norm_pos_iff.2 (hx k)
    have hb : ∀ k, ‖x k‖⁻¹ ≤ ‖x k0‖⁻¹ := fun k =>
      inv_anti₀ (hpos k0) (hk0 k (Finset.mem_univ k))
    have h1 : iteratedFDeriv ℂ (j + 1) (g0 D') x =
        D' • iteratedFDeriv ℂ (j + 1) (fun y : Fin (m + 1) → ℂ => ∏ k, (y k)⁻¹) x := by
      have hsm : ContDiffAt ℂ ((j + 1 : ℕ) : WithTop ℕ∞)
          (D' • fun y : Fin (m + 1) → ℂ => ∏ k, (y k)⁻¹) x := (a_contDiffAt_prod _ x hx).const_smul D'
      rw [phase_function_eq_sum_add_prod_inv, iteratedFDeriv_add_apply (a_contDiff_lin _).contDiffAt hsm, a_lin_zero j hj, zero_add,
        iteratedFDeriv_const_smul_apply (a_contDiffAt_prod _ x hx)]
    rw [h1, norm_smul]
    have h2 := a_prod_bound (j + 1) x hx _ hb
    have h3 : ‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹) ≤ 1 + ‖dg0 D' x‖ := by
      have e : D' / (∏ k, x k) / x k0 = 1 - dg0 D' x k0 := by unfold dg0; ring
      have e2 : ‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹) = ‖D' / (∏ k, x k) / x k0‖ := by
        rw [norm_div, norm_div, norm_prod, Finset.prod_inv_distrib]
        ring
      rw [e2, e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      linarith [norm_le_pi_norm (dg0 D' x) k0]
    have h4 : ‖x k0‖⁻¹ ^ j ≤ (r ^ j)⁻¹ := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le (hxr k0) j)
    have hc := a_cst_nonneg (m + 1) (j + 1)
    calc ‖D'‖ * ‖iteratedFDeriv ℂ (j + 1) (fun y : Fin (m + 1) → ℂ => ∏ k, (y k)⁻¹) x‖
        ≤ ‖D'‖ * (a_cst (m + 1) (j + 1) * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹ ^ (j + 1))) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = a_cst (m + 1) (j + 1) * (‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹)) * ‖x k0‖⁻¹ ^ j := by ring
      _ ≤ a_cst (m + 1) (j + 1) * (1 + ‖dg0 D' x‖) * (r ^ j)⁻¹ := by
          have h5 : 0 ≤ ‖D'‖ * ((∏ k, ‖x k‖⁻¹) * ‖x k0‖⁻¹) := by positivity
          have h6 : 0 ≤ ‖x k0‖⁻¹ ^ j := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left h3 hc) h4 h6
            (mul_nonneg hc (h5.trans h3))
end Formalism.FourierDecayAlt.P
