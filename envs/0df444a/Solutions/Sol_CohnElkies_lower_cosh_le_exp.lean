-- Prove2me | solution 1 for CohnElkies.lower_cosh_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/6af67238-8adf-49c2-8b3e-5592bcd07aac

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  have hnegative : Real.exp (-x) ≤ Real.exp x :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.cosh_eq]
  linarith
end CohnElkies
