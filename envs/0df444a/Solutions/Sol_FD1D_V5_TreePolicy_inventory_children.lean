-- Prove2me | solution 1 for FD1D.V5.TreePolicy.inventory_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:36.140328+00:00
-- url     : https://prove2.me/submissions/984fd6c4-67bd-491c-97cf-d6f568c938ad

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    inventory I d v =
      inventory I (d + 1) (leftChild v) +
        inventory I (d + 1) (rightChild v) := by
  unfold inventory
  exact_mod_cast I.count_children d hdL v
end FD1D.V5.TreePolicy
