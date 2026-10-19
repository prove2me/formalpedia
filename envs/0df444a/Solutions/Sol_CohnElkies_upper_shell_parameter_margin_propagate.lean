-- Prove2me | solution 1 for CohnElkies.upper_shell_parameter_margin_propagate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/da043f49-9247-4a9a-ade4-5900d6dfdc68

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
namespace CohnElkies
theorem _root_.solution
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
  let q : ℝ := δ - ε / 2
  have hq : 0 ≤ q := by
    try dsimp [q]
    linarith
  have hexp :
      Real.exp (q * shortEndpoint ε) ≤
        Real.exp (q * shellLocation ε) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hseparation hq)
  have hfactor :
      0 ≤ (1 / 5000 : ℝ) * shellWeight ε *
        Real.exp ((ε / 2) * shellLocation ε) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (shellWeight_pos ε).le)
      (Real.exp_pos _).le
  calc
    upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) =
      (upperShellShortCoefficient ε *
        Real.exp ((ε / 2) * shortEndpoint ε)) *
          Real.exp (q * shortEndpoint ε) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      try dsimp [q]
      ring
    _ ≤ ((1 / 5000 : ℝ) * shellWeight ε *
        Real.exp ((ε / 2) * shellLocation ε)) *
          Real.exp (q * shortEndpoint ε) :=
      mul_le_mul_of_nonneg_right hmargin
        (Real.exp_pos _).le
    _ ≤ ((1 / 5000 : ℝ) * shellWeight ε *
        Real.exp ((ε / 2) * shellLocation ε)) *
          Real.exp (q * shellLocation ε) :=
      mul_le_mul_of_nonneg_left hexp hfactor
    _ = (1 / 5000 : ℝ) * shellWeight ε *
        Real.exp (δ * shellLocation ε) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      try dsimp [q]
      ring
end CohnElkies
