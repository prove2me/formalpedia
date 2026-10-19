-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_dimension_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/eff6a339-8248-4e6e-9819-8b80a074e7b1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_antitoneOn
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger_antitoneOn

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
    {d : ℕ} (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog ((d : ℝ) / 2) R)
      (Ioi (0 : ℝ)) := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_antitoneOn k R
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_antitoneOn k R
end CohnElkies
