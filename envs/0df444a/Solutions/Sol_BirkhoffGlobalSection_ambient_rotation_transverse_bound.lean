-- Prove2me | solution 1 for BirkhoffGlobalSection.ambient_rotation_transverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T17:51:25.803883+00:00
-- url     : https://prove2.me/submissions/84cbf5b3-2e52-4822-8f93-cffd937780de

import Theorems.Thm_BirkhoffGlobalSection_ambient_angle_base_frame_comparison
import Theorems.Thm_BirkhoffGlobalSection_ambient_angle_shift_stability

open BirkhoffGlobalSection

open scoped ContDiff

set_option autoImplicit false

theorem solution
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ v : Phase, fderiv ℝ F (x 0) v = 0 →
      transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0 →
      ∀ θ : ℝ → ℝ, Continuous θ →
        (∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
          transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
            ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) →
        ∀ a : ℝ, α (a + T) - α a ≤ θ T - θ 0 + 4 * Real.pi := by
  intro v hv htrans θ hθ hpol a
  have h1 := ambient_angle_base_frame_comparison F S x T hx hregular Y hY α hα
    v hv htrans θ hθ hpol
  have h2 := ambient_angle_shift_stability F S x T hx
    (fun t => (hregular t).1) Y hY α hα a
  linarith
