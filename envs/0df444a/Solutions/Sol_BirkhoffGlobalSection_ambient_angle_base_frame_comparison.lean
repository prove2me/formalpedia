-- Prove2me | solution 1 for BirkhoffGlobalSection.ambient_angle_base_frame_comparison
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T20:15:36.629207+00:00
-- url     : https://prove2.me/submissions/109d8ea5-fc75-416d-ac31-e0a3d397e834

import Theorems.Thm_BirkhoffGlobalSection_transverse_frame_path_regular
import Theorems.Thm_BirkhoffGlobalSection_regular_frame_angle_comparison

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
        α T - α 0 ≤ θ T - θ 0 + 2 * Real.pi := by
  intro v hv htrans θ hθ hpol
  obtain ⟨hdet1, hz1, hzne⟩ :=
    transverse_frame_path_regular F S x T hx hregular Y hY v hv htrans
  exact regular_frame_angle_comparison F S x T hx hregular Y hY α hα v hv
    htrans θ hθ hpol hdet1 hz1 hzne
