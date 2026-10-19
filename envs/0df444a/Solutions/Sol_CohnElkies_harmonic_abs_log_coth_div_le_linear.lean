-- Prove2me | solution 1 for CohnElkies.harmonic_abs_log_coth_div_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/8287532a-8fac-4037-9982-88b5f22a96c7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_abs_log_coth_div_le
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
    {x : ℝ} (hx : 2 ≤ x) :
    |Real.log
      (lowerCoth (Real.pi * (x / 2)) / (x / 2))| ≤
      Real.pi * x + |Real.log Real.pi| + x := by
  have hcorr := lower_abs_log_coth_div_le
    (show 0 < x / 2 by linarith)
  have hlog := harmonic_abs_log_half_le_half hx
  nlinarith
end CohnElkies
