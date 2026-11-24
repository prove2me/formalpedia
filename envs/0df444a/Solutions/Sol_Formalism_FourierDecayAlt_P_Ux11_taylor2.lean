-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.taylor2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:55.776183+00:00
-- url     : https://prove2.me/submissions/61014bdb-3424-4ff3-8767-7a7c80cd6f9f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_lip_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution {f : X → E} {x₀ : X} {r M : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ f y)
    (hd2 : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ (fderiv ℝ f) y)
    (hb : ∀ y ∈ Metric.ball x₀ r, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M) {h : X} (hh : ‖h‖ < r) :
    ‖f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h‖ ≤ M * ‖h‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg h) hh
  have hx₀ : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb x₀ hx₀)
  have hsub : Metric.closedBall x₀ ‖h‖ ⊆ Metric.ball x₀ r := Metric.closedBall_subset_ball hh
  have key : ‖(f (x₀ + h) - fderiv ℝ f x₀ (x₀ + h)) - (f x₀ - fderiv ℝ f x₀ x₀)‖ ≤
      M * ‖h‖ * ‖x₀ + h - x₀‖ :=
    (convex_closedBall x₀ ‖h‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => f y - fderiv ℝ f x₀ y) (f' := fun y => fderiv ℝ f y - fderiv ℝ f x₀) (C := M * ‖h‖)
      (fun y hy => ((hd y (hsub hy)).hasFDerivAt.sub (fderiv ℝ f x₀).hasFDerivAt).hasFDerivWithinAt)
      (fun y hy => by
        have h1 := lip_ball hd2 hb (hsub hy)
        have h2 : ‖y - x₀‖ ≤ ‖h‖ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hy
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hM))
      (Metric.mem_closedBall_self (norm_nonneg h))
      (show x₀ + h ∈ Metric.closedBall x₀ ‖h‖ by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  have e : (f (x₀ + h) - fderiv ℝ f x₀ (x₀ + h)) - (f x₀ - fderiv ℝ f x₀ x₀) =
      f (x₀ + h) - f x₀ - fderiv ℝ f x₀ h := by rw [map_add]; abel
  rw [e, add_sub_cancel_left] at key
  calc _ ≤ M * ‖h‖ * ‖h‖ := key
    _ = M * ‖h‖ ^ 2 := by ring
end Formalism.FourierDecayAlt.P.Ux11
