-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/d20d288b-028f-4c91-ba40-d022390ff482

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_neg
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_neg

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
    {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R (-y) =
      lowerGammaBoundaryLog ((d : ℝ) / 2) R y := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_neg k R hy
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_neg k R hy
end CohnElkies
