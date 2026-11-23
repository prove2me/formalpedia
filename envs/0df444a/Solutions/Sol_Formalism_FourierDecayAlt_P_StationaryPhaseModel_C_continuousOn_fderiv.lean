-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.C_continuousOn_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:25.408802+00:00
-- url     : https://prove2.me/submissions/a48a31fa-949e-4fc9-b956-0d162d707e65

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_C_norm_fderiv_le

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
theorem _root_.solution [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) : ContinuousOn (fderiv ℂ f) U := by
  have := FiniteDimensional.proper ℂ E
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set ρ := ρ0 / 3 with hρ
  have hρpos : 0 < ρ := by positivity
  have hsub : closedBall x (2 * ρ) ⊆ U := (closedBall_subset_ball (by rw [hρ]; linarith)).trans hball
  have hdf : ∀ y ∈ U, DifferentiableAt ℂ f y := fun y hy => (hf y hy).differentiableAt (hU.mem_nhds hy)
  have huc : UniformContinuousOn f (closedBall x (2 * ρ)) :=
    (isCompact_closedBall x (2 * ρ)).uniformContinuousOn_of_continuous (hf.continuousOn.mono hsub)
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := Metric.uniformContinuousOn_iff.1 huc (ε * ρ / 2) (by positivity)
  refine ⟨min η ρ, lt_min hη hρpos, fun x' hx' => ?_⟩
  have hx'η : ‖x' - x‖ < η := by rw [← dist_eq_norm]; exact hx'.trans_le (min_le_left _ _)
  have hx'ρ : ‖x' - x‖ < ρ := by rw [← dist_eq_norm]; exact hx'.trans_le (min_le_right _ _)
  have hin1 : ∀ z ∈ ball x ρ, z ∈ closedBall x (2 * ρ) := fun z hz =>
    ball_subset_closedBall (ball_subset_ball (by linarith) hz)
  have hin2 : ∀ z ∈ ball x ρ, z + (x' - x) ∈ closedBall x (2 * ρ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z + (x' - x) - x‖ = ‖(z - x) + (x' - x)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖x' - x‖ := norm_add_le _ _
      _ ≤ 2 * ρ := by linarith
  have hd2 : ∀ z ∈ ball x ρ, HasFDerivAt (fun z => f (z + (x' - x))) (fderiv ℂ f (z + (x' - x))) z := by
    intro z hz
    have := (hdf _ (hsub (hin2 z hz))).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const (x' - x))
    simpa [Function.comp_def] using this
  have hxx : x ∈ ball x ρ := mem_ball_self hρpos
  have hfd : fderiv ℂ (fun z => f (z + (x' - x)) - f z) x = fderiv ℂ f x' - fderiv ℂ f x := by
    have h0 : HasFDerivAt (fun z => f (z + (x' - x)) - f z)
        (fderiv ℂ f (x + (x' - x)) - fderiv ℂ f x) x := (hd2 x hxx).sub (hdf x hx).hasFDerivAt
    rw [h0.fderiv]; congr 2; abel
  rw [dist_eq_norm, ← hfd]
  have hle : ‖fderiv ℂ (fun z => f (z + (x' - x)) - f z) x‖ ≤ (ε * ρ / 2) / ρ := by
    refine C_norm_fderiv_le hρpos ?_ ?_
    · intro z hz
      exact ((hd2 z hz).differentiableAt.sub (hdf z (hsub (hin1 z hz)))).differentiableWithinAt
    · intro z hz
      rw [← dist_eq_norm]
      refine (hηε _ (hin2 z hz) _ (hin1 z hz) ?_).le
      rw [dist_eq_norm, add_sub_cancel_left]; exact hx'η
  have : (ε * ρ / 2) / ρ = ε / 2 := by field_simp
  rw [this] at hle
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
