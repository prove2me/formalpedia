-- Prove2me | solution 1 for CohnElkies.lower_sinh_ge_exp_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/8f849e2b-a07d-4faf-a2cb-0275dc1c9ae3

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
theorem _root_.solution
    {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  have hbig : 2 ≤ Real.exp x := by
    nlinarith [Real.add_one_le_exp x]
  have hsmall : Real.exp (-x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith
end CohnElkies
