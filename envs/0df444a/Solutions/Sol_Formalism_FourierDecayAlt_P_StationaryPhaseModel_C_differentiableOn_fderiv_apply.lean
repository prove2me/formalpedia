-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.C_differentiableOn_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:15.630294+00:00
-- url     : https://prove2.me/submissions/bd67389e-9a3d-4ca2-ae7d-2a692ce8e6a9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_line_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_continuousOn_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution [FiniteDimensional ℂ E] [CompleteSpace F] {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := by
  have := FiniteDimensional.proper ℂ E
  by_cases hv : v = 0
  · subst hv
    simp
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  intro x₁ hx₁
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 hU x₁ hx₁
  set ρ := ρ0 / 3 with hρ
  have hρpos : 0 < ρ := by positivity
  set R := ρ / ‖v‖ with hR
  have hRpos : 0 < R := by positivity
  have hsub : closedBall x₁ (2 * ρ) ⊆ U := (closedBall_subset_ball (by rw [hρ]; linarith)).trans hball
  have hmem : ∀ x ∈ ball x₁ ρ, ∀ z ∈ closedBall (0:ℂ) R, x + z • v ∈ closedBall x₁ (2 * ρ) := by
    intro x hx z hz
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hx
    have hz' : ‖z‖ ≤ R := by simpa using hz
    have h1 : ‖z • v‖ ≤ ρ := by
      rw [norm_smul]
      calc ‖z‖ * ‖v‖ ≤ R * ‖v‖ := by gcongr
        _ = ρ := by rw [hR]; field_simp
    calc ‖x + z • v - x₁‖ = ‖(x - x₁) + z • v‖ := by congr 1; abel
      _ ≤ ‖x - x₁‖ + ‖z • v‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hdf : ∀ y ∈ U, DifferentiableAt ℂ f y := fun y hy => (hf y hy).differentiableAt (hU.mem_nhds hy)
  have hcirc : ∀ θ : ℝ, circleMap 0 R θ ∈ closedBall (0:ℂ) R := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 hRpos.le θ)
  have hform : ∀ x ∈ ball x₁ ρ, fderiv ℂ f x v =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0, R), ((z - 0) ^ 2)⁻¹ • f (x + z • v) := by
    intro x hx
    have hopen : IsOpen ((fun z : ℂ => x + z • v) ⁻¹' U) := hU.preimage (by fun_prop)
    have h1 := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hopen
      (c := 0) (w₀ := 0) (R := R) (f := fun z => f (x + z • v)) (fun z hz => hsub (hmem x hx z hz))
      (fun z hz => (C_line_hasDerivAt (hdf _ hz)).differentiableAt.differentiableWithinAt)
      (mem_ball_self hRpos)
    have hx0 : DifferentiableAt ℂ f (x + (0:ℂ) • v) :=
      hdf _ (hsub (hmem x hx 0 (mem_closedBall_self hRpos.le)))
    rw [h1, (C_line_hasDerivAt hx0).deriv]
    simp
  obtain ⟨B, hB⟩ := (isCompact_closedBall x₁ (2 * ρ)).exists_bound_of_continuousOn
    ((C_continuousOn_fderiv hU hf).mono hsub)
  have hc1 : Continuous fun θ : ℝ => deriv (circleMap 0 R) θ := by
    have : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
      funext θ; rw [deriv_circleMap]
    rw [this]
    exact (continuous_circleMap 0 R).mul continuous_const
  have hc2 : Continuous fun θ : ℝ => ((circleMap 0 R θ - 0) ^ 2)⁻¹ := by
    refine Continuous.inv₀ (((continuous_circleMap 0 R).sub continuous_const).pow 2) fun θ => ?_
    exact pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hRpos.ne'))
  have hcF : ∀ x ∈ ball x₁ ρ, Continuous fun θ : ℝ => f (x + circleMap 0 R θ • v) := by
    intro x hx
    refine hf.continuousOn.comp_continuous ?_ fun θ => hsub (hmem x hx _ (hcirc θ))
    exact continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)
  have hcF' : Continuous fun θ : ℝ => fderiv ℂ f (x₁ + circleMap 0 R θ • v) := by
    refine (C_continuousOn_fderiv hU hf).comp_continuous ?_
      fun θ => hsub (hmem x₁ (mem_ball_self hρpos) _ (hcirc θ))
    exact continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)
  have hder : HasFDerivAt (fun x => ∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • f (x + circleMap 0 R θ • v)))
      (∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • fderiv ℂ f (x₁ + circleMap 0 R θ • v))) x₁ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (F' := fun x θ => deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • fderiv ℂ f (x + circleMap 0 R θ • v)))
      (bound := fun θ => ‖deriv (circleMap 0 R) θ‖ * (‖((circleMap 0 R θ - 0) ^ 2)⁻¹‖ * B))
      (ball_mem_nhds x₁ hρpos) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [ball_mem_nhds x₁ hρpos] with x hx
      exact (hc1.smul (hc2.smul (hcF x hx))).aestronglyMeasurable
    · exact (hc1.smul (hc2.smul (hcF x₁ (mem_ball_self hρpos)))).intervalIntegrable _ _
    · exact (hc1.smul (hc2.smul hcF')).aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ x hx => ?_
      rw [norm_smul, norm_smul]
      gcongr
      exact hB _ (hmem x hx _ (hcirc θ))
    · exact (hc1.norm.mul (hc2.norm.mul continuous_const)).intervalIntegrable _ _
    · refine Eventually.of_forall fun θ _ x hx => ?_
      have h1 := (hdf _ (hsub (hmem x hx _ (hcirc θ)))).hasFDerivAt.comp x
        ((hasFDerivAt_id x).add_const (circleMap 0 R θ • v))
      have h2 : HasFDerivAt (fun x => f (x + circleMap 0 R θ • v))
          (fderiv ℂ f (x + circleMap 0 R θ • v)) x := by
        simpa [Function.comp_def] using h1
      exact (h2.const_smul _).const_smul _
  have hev : (fun x => fderiv ℂ f x v) =ᶠ[𝓝 x₁] fun x => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap 0 R) θ •
        (((circleMap 0 R θ - 0) ^ 2)⁻¹ • f (x + circleMap 0 R θ • v)) := by
    filter_upwards [ball_mem_nhds x₁ hρpos] with x hx
    rw [hform x hx]
    rfl
  exact (hev.differentiableAt_iff).2 (hder.differentiableAt.const_smul _)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
