-- Prove2me | solution 1 for CohnElkies.lowerCoth_log_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/839cc953-fd01-4365-aa74-b20e754f99c4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_pos
import Theorems.Thm_CohnElkies_lowerCoth_antitoneOn

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution :
    AntitoneOn (fun x : ℝ => Real.log (lowerCoth x))
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  exact Real.log_le_log (lowerCoth_pos hy)
    (lowerCoth_antitoneOn hx hy hxy)
end CohnElkies
