-- Prove2me | solution 2 for CohnElkies.upper_shell_parameter_margin_propagate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:51.329322+00:00
-- url     : https://prove2.me/submissions/28c5a164-6078-4915-92c1-8243e4327a10

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε δ : ℝ}
    (hδ : ε / 2 ≤ δ)
    (hseparation : shortEndpoint ε ≤ shellLocation ε)
    (hmargin :
      upperShellShortCoefficient ε *
          Real.exp ((ε / 2) * shortEndpoint ε) ≤
        (1 / 5000 : ℝ) * shellWeight ε *
          Real.exp ((ε / 2) * shellLocation ε)) :
    upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) ≤
      (1 / 5000 : ℝ) * shellWeight ε *
        Real.exp (δ * shellLocation ε) := by
  have hW : 0 < shellWeight ε := by unfold shellWeight; positivity
  have hE : Real.exp (δ * shortEndpoint ε) = Real.exp ((ε / 2) * shortEndpoint ε) * Real.exp ((δ - ε / 2) * shortEndpoint ε) := by
    rw [← Real.exp_add]; congr 1; ring
  have hL : Real.exp (δ * shellLocation ε) = Real.exp ((ε / 2) * shellLocation ε) * Real.exp ((δ - ε / 2) * shellLocation ε) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp ((δ - ε / 2) * shortEndpoint ε) ≤ Real.exp ((δ - ε / 2) * shellLocation ε) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hseparation (by linarith))
  have hp1 := Real.exp_pos ((δ - ε / 2) * shortEndpoint ε)
  have hp2 := Real.exp_pos ((ε / 2) * shellLocation ε)
  rw [hE, hL]
  calc upperShellShortCoefficient ε * (Real.exp (ε / 2 * shortEndpoint ε) * Real.exp ((δ - ε / 2) * shortEndpoint ε))
      = (upperShellShortCoefficient ε * Real.exp (ε / 2 * shortEndpoint ε)) * Real.exp ((δ - ε / 2) * shortEndpoint ε) := by ring
    _ ≤ ((1 / 5000 : ℝ) * shellWeight ε * Real.exp ((ε / 2) * shellLocation ε)) * Real.exp ((δ - ε / 2) * shortEndpoint ε) :=
        mul_le_mul_of_nonneg_right hmargin hp1.le
    _ ≤ ((1 / 5000 : ℝ) * shellWeight ε * Real.exp ((ε / 2) * shellLocation ε)) * Real.exp ((δ - ε / 2) * shellLocation ε) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

