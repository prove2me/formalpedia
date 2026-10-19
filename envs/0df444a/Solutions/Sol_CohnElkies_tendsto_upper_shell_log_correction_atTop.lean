-- Prove2me | solution 1 for CohnElkies.tendsto_upper_shell_log_correction_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/26e5e77d-e019-458e-99fb-456473db09f2

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
    Tendsto (fun x : ℝ =>
      Real.exp (5 * Real.log x / x))
      atTop (𝓝 (1 : ℝ)) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using!
      Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
  have hscaled : Tendsto (fun x : ℝ =>
      5 * Real.log x / x)
      atTop (𝓝 (0 : ℝ)) := by
    convert! hlog.const_mul (5 : ℝ) using 1
    · ext x
      ring
    · norm_num
  simpa using! hscaled.rexp
end CohnElkies
