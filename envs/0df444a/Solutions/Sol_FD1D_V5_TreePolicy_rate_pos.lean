-- Prove2me | solution 1 for FD1D.V5.TreePolicy.rate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:17.463802+00:00
-- url     : https://prove2.me/submissions/3fa9ed58-0a27-401c-85de-71bb60ef29be

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_node_invariants

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 < rate I a d v :=
  (node_invariants I ha hm d hdL v).1
end FD1D.V5.TreePolicy
