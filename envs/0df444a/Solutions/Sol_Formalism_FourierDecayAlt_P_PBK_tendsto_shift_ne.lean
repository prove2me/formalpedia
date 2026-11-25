-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_shift_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:07.088392+00:00
-- url     : https://prove2.me/submissions/ac3af4ff-92bd-4b23-aa6b-45ae6303cfb2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_rhoR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s : ℕ) (hs : 1 ≤ s) (σ ζ : ℂ) (hζ : ζ ≠ 1) :
    Tendsto (fun x => ζ * rhoR s σ x * (x + σ) - x) (cocompact ℂ) (cocompact ℂ) := by
  have hρ := Formalism.FourierDecayAlt.P.PBK.tendsto_rhoR s σ
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hA : ∀ᶠ x in cocompact ℂ, ‖ζ - 1‖ / 2 < ‖ζ * rhoR s σ x - 1‖ := by
    have h2 : Tendsto (fun x => ‖ζ * rhoR s σ x - 1‖) (cocompact ℂ) (𝓝 ‖ζ * 1 - 1‖) :=
      ((hρ.const_mul ζ).sub_const 1).norm
    rw [mul_one] at h2
    exact h2.eventually (lt_mem_nhds (by linarith))
  have hB : ∀ᶠ x in cocompact ℂ, ‖ζ * rhoR s σ x * σ‖ < ‖ζ * σ‖ + 1 := by
    have h2 : Tendsto (fun x => ‖ζ * rhoR s σ x * σ‖) (cocompact ℂ) (𝓝 ‖ζ * 1 * σ‖) :=
      ((hρ.const_mul ζ).mul_const σ).norm
    rw [mul_one] at h2
    exact h2.eventually (gt_mem_nhds (by linarith))
  have hc : comap norm atTop = cocompact ℂ := by rw [comap_norm_atTop, Metric.cobounded_eq_cocompact]
  refine (tendsto_comap_iff.mpr ?_).mono_right hc.le
  have hlow : Tendsto (fun x : ℂ => ‖ζ - 1‖ / 2 * ‖x‖ + -(‖ζ * σ‖ + 1)) (cocompact ℂ) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop (by linarith))
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [hA, hB] with x hxA hxB

  have heq : ζ * rhoR s σ x * (x + σ) - x = (ζ * rhoR s σ x - 1) * x + ζ * rhoR s σ x * σ := by ring
  have htri := norm_add_le ((ζ * rhoR s σ x - 1) * x + ζ * rhoR s σ x * σ) (-(ζ * rhoR s σ x * σ))
  rw [add_neg_cancel_right, norm_neg, norm_mul] at htri
  have hmul : ‖ζ - 1‖ / 2 * ‖x‖ ≤ ‖ζ * rhoR s σ x - 1‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right hxA.le (norm_nonneg _)
  simp only [Function.comp_apply, heq]
  linarith
end Formalism.FourierDecayAlt.P.PBK
