-- Prove2me | solution 1 for CohnElkies.stripPoissonKernel_mul_abs_lowerRiemannLog_zero_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/d553068e-4333-434b-ac82-e92351271fa9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripPoissonKernel_pos
import Theorems.Thm_CohnElkies_stripPoissonKernel_mul_lowerRiemannLog_zero_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ =>
      stripPoissonKernel σ T * |lowerRiemannLog T 0|) := by
  have h :=
    (stripPoissonKernel_mul_lowerRiemannLog_zero_integrable
      hbelow habove).abs
  apply h.congr
  filter_upwards [] with T
  rw [abs_mul,
    abs_of_pos (stripPoissonKernel_pos hbelow habove T)]
end CohnElkies
