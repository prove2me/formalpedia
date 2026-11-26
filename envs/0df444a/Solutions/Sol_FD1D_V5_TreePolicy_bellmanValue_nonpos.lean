-- Prove2me | solution 1 for FD1D.V5.TreePolicy.bellmanValue_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:42.489592+00:00
-- url     : https://prove2.me/submissions/26f9c34a-7bac-442e-983f-3a914a517794

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_le_half
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_pos
import Theorems.Thm_FD1D_V5_LocalPolicy_bellman_nonpos


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    bellmanValue I a d v ≤ 0 := by
  unfold bellmanValue
  exact bellman_nonpos (regularizedMass_pos I ha d v).le
    (discrepancy_le_half I ha hm hdL v)
end FD1D.V5.TreePolicy
