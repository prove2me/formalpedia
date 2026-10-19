-- Prove2me | solution 1 for CohnElkies.tendsto_upperShellMarginRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/ca77072f-2672-4002-97d5-02358c711282

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperShellMarginRatio_inv
import Theorems.Thm_CohnElkies_tendsto_upper_log_cubic_gaussian_atTop
import Theorems.Thm_CohnElkies_tendsto_upper_shell_log_correction_atTop

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
    Tendsto upperShellMarginRatio
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  have hproduct :
      Tendsto (fun x : ℝ =>
        (5000 * ((10 * Real.log x + x ^ 3) *
          Real.exp (-(x ^ 2) / 8))) *
            Real.exp (5 * Real.log x / x))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using!
      (tendsto_upper_log_cubic_gaussian_atTop.const_mul
        (5000 : ℝ)).mul
          tendsto_upper_shell_log_correction_atTop
  refine hproduct.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  rw [upperShellMarginRatio_inv hx]
  ring
end CohnElkies
