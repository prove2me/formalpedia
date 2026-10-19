-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_integer_riemann_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/b33a90ae-98bc-40be-bd0e-9807759338b0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_nonneg
import Theorems.Thm_CohnElkies_lower_integer_leftRiemann_error
import Theorems.Thm_CohnElkies_integral_lowerRiemannLog
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer_scaled

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
    {k : ℕ} (hk : 0 < k) {R T : ℝ}
    (hR : 0 < R) (hT : T ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R ((k : ℝ) * T) ≤
      (k : ℝ) *
        (Real.log (Real.pi * R ^ 2 / (k : ℝ)) +
          1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  rw [lowerGammaBoundaryLog_integer_scaled hk hR hT]
  have hriemann := (lower_integer_leftRiemann_error hT hk).2
  have hphase := integral_lowerRiemannLog hT
  have hcoth := lowerCoth_log_nonneg
    (show 0 < Real.pi * |T| / 2 by positivity)
  unfold lowerRiemannErrorMajorant
  nlinarith [le_abs_self (lowerRiemannLog T 1),
    neg_le_abs (lowerRiemannLog T 0),
    abs_nonneg (lowerRiemannLog T 0),
    abs_nonneg (lowerRiemannLog T 1)]
end CohnElkies
