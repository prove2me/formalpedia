-- Prove2me | solution 1 for CohnElkies.tendsto_log_two_mul_nat_div_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/1e3c3639-8d84-40d5-b257-14f98f07ef4c

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
    Tendsto (fun k : ℕ =>
      Real.log ((2 : ℝ) * (k : ℝ)) / (k : ℝ))
      atTop (nhds 0) := by
  have hsum :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log (2 : ℝ))).add
      tendsto_log_nat_div_nat
  have hsum' :
      Tendsto
        (fun k : ℕ =>
          Real.log (2 : ℝ) / (k : ℝ) +
            Real.log (k : ℝ) / (k : ℝ))
        atTop (nhds 0) := by
    simpa using! hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  rw [← add_div, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by exact_mod_cast (Nat.ne_of_gt hk))]
end CohnElkies
