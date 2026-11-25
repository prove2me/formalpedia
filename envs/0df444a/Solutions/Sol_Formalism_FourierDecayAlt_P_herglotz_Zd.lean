-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.herglotz_Zd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:51:00.46488+00:00
-- url     : https://prove2.me/submissions/63125a74-1be6-4e5d-9a61-36fd610f0b22

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_norm_ee
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_ee_mul_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_dsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_tendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_wt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.H.HerglotzZd := by
  intro d A hA hpos x
  change 0 ≤ (∑' σ, A σ * ee x σ).re
  have hN : ∀ N : ℕ, N ≠ 0 → 0 ≤ (∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)).re := by
    intro N hN
    have h := hpos (box d N) (fun σ => ee x σ)
    have h2 : ∑ σ ∈ box d N, ∑ σ' ∈ box d N, A (σ - σ') * ee x σ * starRingEnd ℂ (ee x σ')
        = ∑ σ ∈ box d N, ∑ σ' ∈ box d N, (fun τ => A τ * ee x τ) (σ - σ') := by
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
      simp only
      rw [mul_assoc, ee_mul_conj]
    rw [h2, dsum (fun τ => A τ * ee x τ) (box d N)] at h
    have h3 : ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)
        = ((((N : ℝ) ^ d)⁻¹ : ℝ) : ℂ) * ∑' τ,
            ((((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * (A τ * ee x τ)) := by
      rw [← tsum_mul_left]
      congr 1
      funext τ
      rw [← wt_eq N hN τ]
      push_cast
      ring
    rw [h3, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) h
  have hlim : Tendsto (fun N : ℕ => ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)) atTop
      (𝓝 (∑' τ, A τ * ee x τ)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun τ => ‖A τ‖) hA ?_ ?_
    · intro τ
      have := ((Complex.continuous_ofReal.tendsto 1).comp (wt_tendsto τ)).mul_const (A τ * ee x τ)
      simpa using this
    · refine Eventually.of_forall fun N τ => ?_
      rw [norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (wt_nonneg N τ)]
      nlinarith [wt_le_one N τ, norm_nonneg (A τ)]
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    (by filter_upwards [eventually_ne_atTop 0] with N hN' using hN N hN')
end Formalism.FourierDecayAlt.P
