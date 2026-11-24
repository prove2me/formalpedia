-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.one_parameter_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:34:50.744575+00:00
-- url     : https://prove2.me/submissions/ccd55217-874c-447d-8410-7264b30e46e4

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Qr.OneParamDiff := by
  intro W _ _ _ φ h0 hadd hc
  have hmul : ∀ s t, φ (s + t) = φ s * φ t := fun s t => hadd s t
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖φ s - 1‖ < 1 / 2 := by
    obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun s hs => ?_⟩
    have := H s (by rwa [Real.dist_eq, sub_zero])
    rwa [dist_eq_norm, h0] at this
  set h : ℝ := δ / 2 with hh
  have hpos : 0 < h := by positivity
  have hint : ∀ a b : ℝ, IntervalIntegrable φ MeasureTheory.volume a b := fun a b => hc.intervalIntegrable a b
  set M : W →L[ℂ] W := ∫ s in (0 : ℝ)..h, φ s with hM
  have hbound : ‖M - h • (1 : W →L[ℂ] W)‖ ≤ 1 / 2 * |h - 0| := by
    have e : M - h • (1 : W →L[ℂ] W) = ∫ s in (0 : ℝ)..h, (φ s - 1) := by
      rw [intervalIntegral.integral_sub (hint 0 h) intervalIntegrable_const, intervalIntegral.integral_const,
        sub_zero]
    rw [e]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hpos.le] at hs
    refine (hball s ?_).le
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  set tt : W →L[ℂ] W := 1 - h⁻¹ • M with htt
  have hnorm : ‖tt‖ < 1 := by
    have e : tt = h⁻¹ • (h • (1 : W →L[ℂ] W) - M) := by
      rw [htt, smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc h⁻¹ * ‖M - h • (1 : W →L[ℂ] W)‖ ≤ h⁻¹ * (1 / 2 * |h - 0|) := by gcongr
      _ = 1 / 2 := by
        rw [sub_zero, abs_of_pos hpos, ← mul_assoc, mul_comm h⁻¹, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
      _ < 1 := by norm_num
  let u0 := Units.oneSub tt hnorm
  have hu0 : (u0 : W →L[ℂ] W) = h⁻¹ • M := by
    show 1 - tt = h⁻¹ • M
    rw [htt, sub_sub_cancel]
  set G : ℝ → W →L[ℂ] W := fun t => (∫ s in (0 : ℝ)..t + h, φ s) - ∫ s in (0 : ℝ)..t, φ s with hG
  have hφM : ∀ t, φ t * M = G t := by
    intro t
    have e1 := (ContinuousLinearMap.mul ℂ (W →L[ℂ] W) (φ t)).intervalIntegral_comp_comm (hint 0 h)
    simp only [ContinuousLinearMap.mul_apply'] at e1
    rw [hM, ← e1]
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hint 0 (t + h)) (hint 0 t)]
    rw [show (fun s => φ t * φ s) = fun s => φ (t + s) from funext fun s => (hmul t s).symm,
      intervalIntegral.integral_comp_add_left φ t, add_zero]
  have hφ : φ = fun t => (h⁻¹ • G t) * (↑u0⁻¹ : W →L[ℂ] W) := by
    funext t
    rw [← hφM t, ← mul_smul_comm, ← hu0, Units.mul_inv_cancel_right]
  have hF : ∀ x, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, φ s) (φ x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  refine ⟨(h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W), fun t => ?_⟩
  have hGd : HasDerivAt G (φ (t + h) - φ t) t := ((hF (t + h)).comp_add_const t h).sub (hF t)
  let R : (W →L[ℂ] W) →L[ℝ] (W →L[ℂ] W) :=
    (((ContinuousLinearMap.mul ℂ (W →L[ℂ] W)).flip (↑u0⁻¹ : W →L[ℂ] W)).restrictScalars ℝ)
  have hd := R.hasFDerivAt.comp_hasDerivAt t (hGd.const_smul h⁻¹)
  have e : ∀ x, φ x = (⇑R ∘ (h⁻¹ • G)) x := by
    intro x
    rw [hφ]
    rfl
  have e2 : φ t ∘SL ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = R (h⁻¹ • (φ (t + h) - φ t)) := by
    show φ t * ((h⁻¹ • (φ h - 1)) * (↑u0⁻¹ : W →L[ℂ] W)) = (h⁻¹ • (φ (t + h) - φ t)) * (↑u0⁻¹ : W →L[ℂ] W)
    rw [hmul t h, show φ t * φ h - φ t = φ t * (φ h - 1) by rw [mul_sub, mul_one], ← mul_smul_comm, mul_assoc]
  rw [e2]
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall e)
end Formalism.FourierDecayAlt.P
