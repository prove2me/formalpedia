-- Prove2me | solution 1 for CohnElkies.upper_shortShellDensity_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/0a2f989f-e133-47d0-b6ca-b691202add58

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
    {ε δ a A : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A) :
    (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a) ≤
      (1 / 2 : ℝ) * Real.exp (δ * A) := by
  have hmargin : shortMargin ε a ≤ 1 := by
    unfold shortMargin
    nlinarith [mul_nonneg hε.le
      (show 0 ≤ 1 + a by linarith)]
  have hexp : Real.exp (-2 * a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hratio :
      Real.cosh ((1 + δ) * a) / Real.cosh a ≤
        Real.exp (δ * A) :=
    (cosh_ratio_upper ha.le hδ).trans
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left haA hδ))
  have hidentity :
      (-shortShellDensity ε a) * a ^ 2 *
        Real.cosh ((1 + δ) * a) =
          (1 / 2 : ℝ) * shortMargin ε a *
            Real.exp (-2 * a) *
              (Real.cosh ((1 + δ) * a) /
                Real.cosh a) := by
    unfold shortShellDensity
    field_simp [ha.ne', (Real.cosh_pos a).ne']
  rw [hidentity]
  calc
    (1 / 2 : ℝ) * shortMargin ε a *
        Real.exp (-2 * a) *
          (Real.cosh ((1 + δ) * a) /
            Real.cosh a) ≤
      (1 / 2 : ℝ) * 1 * 1 *
        Real.exp (δ * A) := by
      gcongr
    _ = (1 / 2 : ℝ) * Real.exp (δ * A) := by
      ring
end CohnElkies
