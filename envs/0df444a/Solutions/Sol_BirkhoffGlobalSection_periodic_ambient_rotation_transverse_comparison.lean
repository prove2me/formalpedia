-- Prove2me | solution 1 for BirkhoffGlobalSection.periodic_ambient_rotation_transverse_comparison
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T17:33:56.430501+00:00
-- url     : https://prove2.me/submissions/d31e6b25-faa6-4e4e-96bc-1f7ab1042c2b

import Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_angle_exists
import Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_transverse_bound

open BirkhoffGlobalSection

open scoped ContDiff

set_option autoImplicit false

theorem solution
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hregular : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t) ∧ fderiv ℝ F (x t) ≠ 0)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y) :
    ∃ α : ℝ → ℝ, IsAmbientRotationAngle Y α ∧
      ∀ v : Phase, fderiv ℝ F (x 0) v = 0 →
        transverseFrameCoordinates (TangentialHessian.grad F (x 0)) v ≠ 0 →
        ∀ θ : ℝ → ℝ, Continuous θ →
          (∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
            transverseFrameCoordinates (TangentialHessian.grad F (x t)) (Y t v) =
              ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) →
          ∀ a : ℝ, α (a + T) - α a ≤ θ T - θ 0 + 4 * Real.pi := by
  obtain ⟨α, hα⟩ :=
    ambient_rotation_angle_exists F x (fun t => (hregular t).1) Y hY
  exact ⟨α, hα, ambient_rotation_transverse_bound F S x T hx hregular Y hY α hα⟩
