-- Prove2me | solution 1 for CohnElkies.tendsto_saddleSourceGaussianNormalizedTailMajorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/16069757-a449-49af-8cde-77ec138d5b09

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto saddleSourceGaussianNormalizedTailMajorant
      atTop (𝓝 (0 : ℝ)) := by
  have hpower : Tendsto
      (fun x : ℝ => x ^ (1 / 6 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)
  have hnegative : Tendsto
      (fun x : ℝ => -(x ^ (1 / 6 : ℝ)) / 8)
      atTop atBot := by
    have h := hpower.const_mul_atTop_of_neg
      (by norm_num : -(1 / 8 : ℝ) < 0)
    convert! h using 1
    funext x
    ring
  have hexp := Real.tendsto_exp_atBot.comp hnegative
  have h := hexp.const_mul (4 * Real.sqrt (2 * Real.pi))
  change Tendsto
    (fun x : ℝ =>
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(x ^ (1 / 6 : ℝ)) / 8))
    atTop (𝓝 (0 : ℝ))
  simpa only [Function.comp_apply, mul_zero] using! h
end CohnElkies
