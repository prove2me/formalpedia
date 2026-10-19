-- Prove2me | solution 1 for CohnElkies.tendsto_log_nat_div_oddDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/4c18e8bc-ee6b-4c49-b28e-1f3071cb5f6d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_log_nat_div_nat

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
    Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (2 * (k : ℝ) + 1))
      atTop (nhds 0) := by
  have hproduct := tendsto_log_nat_div_nat.mul
    Stirling.tendsto_self_div_two_mul_self_add_one
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (Real.log (k : ℝ) / (k : ℝ)) *
            ((k : ℝ) / (2 * (k : ℝ) + 1)))
        atTop (nhds 0) := by
    convert! hproduct using 1; norm_num
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  field_simp
end CohnElkies
