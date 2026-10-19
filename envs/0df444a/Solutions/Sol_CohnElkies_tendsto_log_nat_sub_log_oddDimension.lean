-- Prove2me | solution 1 for CohnElkies.tendsto_log_nat_sub_log_oddDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/1b3fb8c2-da57-4675-98a5-a9c81cf56b17

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
    Tendsto
      (fun k : ℕ =>
        Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1))
      atTop (nhds (Real.log (1 / 2 : ℝ))) := by
  have hratio :=
    Stirling.tendsto_self_div_two_mul_self_add_one.log
      (by norm_num : (1 / 2 : ℝ) ≠ 0)
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hodd : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  exact Real.log_div hkreal hodd
end CohnElkies
