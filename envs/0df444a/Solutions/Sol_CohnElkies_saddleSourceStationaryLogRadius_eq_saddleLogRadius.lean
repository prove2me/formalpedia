-- Prove2me | solution 1 for CohnElkies.saddleSourceStationaryLogRadius_eq_saddleLogRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/735753ea-b8d6-4ad9-b067-380824bb840b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleLogRadius_eq_digamma_add_shellDerivative

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleSourceStationaryLogRadius ε ((d : ℝ) / 2) u =
      saddleLogRadius ε d u := by
  rw [saddleLogRadius_eq_digamma_add_shellDerivative]
  rfl
end CohnElkies
