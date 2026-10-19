-- Prove2me | solution 1 for CohnElkies.tendsto_log_nat_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/969ee9ad-f493-4623-b868-38258fc10716

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (nhds 0) := by
  simpa using!
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1
      (by norm_num : (1 : ℝ) ≠ 0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
end CohnElkies
