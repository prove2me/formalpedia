-- Prove2me | solution 1 for CohnElkies.harmonic_abs_log_sqrtFactor_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/b4b8b70f-a44f-4492-847f-4f6ee782c972

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_abs_log_sqrtFactor_le
import Theorems.Thm_CohnElkies_harmonic_abs_log_half_le_half

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
    {c x : ℝ} (hc : 0 ≤ c) (hx : 2 ≤ x) :
    |Real.log
      (Real.sqrt (c ^ 2 + (x / 2) ^ 2))| ≤ c + x := by
  have hfactor := lower_abs_log_sqrtFactor_le
    hc (show 0 < x by linarith)
  have hlog := harmonic_abs_log_half_le_half hx
  linarith
end CohnElkies
