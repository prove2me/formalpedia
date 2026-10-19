-- Prove2me | solution 1 for CohnElkies.tendsto_saddleSmallResidueTruncation_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/c35eca8b-25b7-4788-bc23-5600435b72b6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallResidueTruncation_upper
import Theorems.Thm_CohnElkies_tendsto_logLinear_sq_div_atTop

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
    Tendsto
      (fun ℓ : ℝ =>
        (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (f := fun ℓ : ℝ =>
      (saddleSmallResidueTruncation ℓ : ℝ) ^ 2 / ℓ)
    (g := fun ℓ : ℝ =>
      (20 * Real.log ℓ + 1) ^ 2 / ℓ)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)]
      with ℓ hℓ
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)]
      with ℓ hℓ
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact (sq_le_sq₀
      (by exact_mod_cast (Nat.zero_le
        (saddleSmallResidueTruncation ℓ)))
      (by nlinarith [Real.log_nonneg hℓ])).mpr
      (saddleSmallResidueTruncation_upper hℓ)
  · exact tendsto_logLinear_sq_div_atTop
end CohnElkies
