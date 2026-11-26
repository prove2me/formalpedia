-- Prove2me | solution 1 for FD1D.V5.TreePolicy.leaf_deletionMass_pos_of_count_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:12.44384+00:00
-- url     : https://prove2.me/submissions/f0767b46-ee45-4f64-8c09-0773f4786be7

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_pos

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) (v : DyadicNode L)
    (hv : 0 < I.count L v) :
    0 < deletionMass I a L v := by
  unfold deletionMass inventory
  exact mul_pos (by exact_mod_cast hv) (rate_pos I ha hm le_rfl v)
end FD1D.V5.TreePolicy
