-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_differentiableOn_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:41.030847+00:00
-- url     : https://prove2.me/submissions/820be508-faa1-4f8b-af6f-8c1c783aaa91

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_hasDerivAt_line
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_radius
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_continuousOn_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution [CompleteSpace F] {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (v : Fin d → ℂ) :
    DifferentiableOn ℂ (fun x => fderiv ℂ g x v) Ω := by
  intro x₀ hx₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨R, r, hR, hr, hsub, hmem⟩ := hol_radius hΩ hx₀ v
  have hK : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
  have hcf := hol_continuousOn_fderiv hΩ hg
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcf.mono hsub)
  have hs : Metric.ball x₀ (R / 2) ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by positivity)
  have hx0 : x₀ ∈ Metric.ball x₀ (R / 2) := Metric.mem_ball_self (by positivity)
  have hcm : ∀ θ : ℝ, circleMap 0 r θ ∈ Metric.closedBall (0 : ℂ) r := fun θ =>
    Metric.sphere_subset_closedBall (circleMap_mem_sphere 0 hr.le θ)

  let c : ℝ → ℂ := fun θ => deriv (circleMap 0 r) θ * ((circleMap 0 r θ - 0) ^ 2)⁻¹
  have hc : Continuous c := by
    have h1 : Continuous fun θ : ℝ => deriv (circleMap 0 r) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 r).mul continuous_const
    refine h1.mul (Continuous.inv₀ (((continuous_circleMap 0 r).sub continuous_const).pow 2) ?_)
    intro θ
    have := circleMap_ne_center (c := (0 : ℂ)) (θ := θ) hr.ne'
    simpa using this
  have hp : ∀ x : Fin d → ℂ, Continuous fun θ : ℝ => x + circleMap 0 r θ • v := fun x =>
    continuous_const.add ((continuous_circleMap 0 r).smul continuous_const)
  have hFc : ∀ x ∈ Metric.ball x₀ (R / 2), Continuous fun θ : ℝ => c θ • g (x + circleMap 0 r θ • v) :=
    fun x hx => hc.smul (hg.continuousOn.comp_continuous (hp x) fun θ => hsub (hmem x hx _ (hcm θ)))
  have hF'c : Continuous fun θ : ℝ => c θ • fderiv ℂ g (x₀ + circleMap 0 r θ • v) :=
    hc.smul (hcf.comp_continuous (hp x₀) fun θ => hsub (hmem x₀ hx0 _ (hcm θ)))
  have key : HasFDerivAt (fun x => ∫ θ in (0 : ℝ)..2 * Real.pi, c θ • g (x + circleMap 0 r θ • v))
      (∫ θ in (0 : ℝ)..2 * Real.pi, c θ • fderiv ℂ g (x₀ + circleMap 0 r θ • v)) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (F := fun x θ => c θ • g (x + circleMap 0 r θ • v))
      (F' := fun x θ => c θ • fderiv ℂ g (x + circleMap 0 r θ • v))
      (bound := fun θ => ‖c θ‖ * M) hs ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hs] with x hx
      exact (hFc x hx).aestronglyMeasurable
    · exact (hFc x₀ hx0).intervalIntegrable _ _
    · exact hF'c.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _ (hmem x hx _ (hcm θ))) (norm_nonneg _)
    · exact (hc.norm.mul continuous_const).intervalIntegrable _ _
    · refine Filter.Eventually.of_forall fun θ _ x hx => ?_
      have h1 : HasFDerivAt g (fderiv ℂ g (x + circleMap 0 r θ • v)) (x + circleMap 0 r θ • v) :=
        (hg.differentiableAt (hΩ.mem_nhds (hsub (hmem x hx _ (hcm θ))))).hasFDerivAt
      exact ((hasFDerivAt_comp_add_right (circleMap 0 r θ • v)).mpr h1).const_smul (c θ)
  have heq : (fun x => fderiv ℂ g x v) =ᶠ[nhds x₀]
      fun x => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, c θ • g (x + circleMap 0 r θ • v) := by
    filter_upwards [hs] with x hx
    have hU : IsOpen {ζ : ℂ | x + ζ • v ∈ Ω} :=
      hΩ.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have hdU : DifferentiableOn ℂ (fun ζ : ℂ => g (x + ζ • v)) {ζ : ℂ | x + ζ • v ∈ Ω} := fun ζ hζ =>
      (hol_hasDerivAt_line hΩ hg x v ζ hζ).differentiableAt.differentiableWithinAt
    have h1 := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU
      (c := 0) (w₀ := 0) (R := r) (fun ζ hζ => hsub (hmem x hx ζ hζ)) hdU (Metric.mem_ball_self hr)
    have h2 := (hol_hasDerivAt_line hΩ hg x v 0 (by
      simpa using hsub (hmem x hx 0 (Metric.mem_closedBall_self hr.le)))).deriv
    simp only [zero_smul, add_zero] at h2
    rw [← h2, ← h1]
    simp only [circleIntegral, c, smul_smul]
  exact (key.const_smul _).differentiableAt.congr_of_eventuallyEq heq
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
