-- Prove2me | solution 1 for BirkhoffGlobalSection.ambient_angle_shift_stability
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T19:36:21.448125+00:00
-- url     : https://prove2.me/submissions/3b570274-511f-42af-9b21-6016c6b85b89

import Theorems.Thm_BirkhoffGlobalSection_variational_flow_period_cocycle
import Theorems.Thm_BirkhoffGlobalSection_variational_cocycle_angle_defect

open BirkhoffGlobalSection

open scoped ContDiff

set_option autoImplicit false

theorem solution
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hF : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t))
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y)
    (α : ℝ → ℝ) (hα : IsAmbientRotationAngle Y α) :
    ∀ a : ℝ, α (a + T) - α a ≤ α T - α 0 + 2 * Real.pi := by
  obtain ⟨hper, hcocycle⟩ :=
    variational_flow_period_cocycle F S x T hx hF Y hY
  exact variational_cocycle_angle_defect F x T hper Y hY hcocycle α hα
