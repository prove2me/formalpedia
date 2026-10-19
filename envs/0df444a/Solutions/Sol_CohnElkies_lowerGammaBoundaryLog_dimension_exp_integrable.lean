-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/af2572ea-0690-4265-be90-fe2ccc46de3d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_exp_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_exp_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y) := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_exp_integrable ha k R
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_exp_integrable ha k R
end CohnElkies
