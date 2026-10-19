-- Prove2me | solution 1 for CohnElkies.harmonic_abs_log_half_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/2bd1fac3-be09-44ca-a541-528ef008393b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (x / 2)| ≤ x / 2 := by
  have hhalf : 1 ≤ x / 2 := by linarith
  rw [abs_of_nonneg (Real.log_nonneg hhalf)]
  have hlog :=
    Real.log_le_sub_one_of_pos
      (show 0 < x / 2 by linarith)
  linarith
end CohnElkies
