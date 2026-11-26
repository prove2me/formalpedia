-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedIndex_transition_eq_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:34.775142+00:00
-- url     : https://prove2.me/submissions/61544784-7d54-481c-8125-cec8c1b26167

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
attribute [local simp] FD1D.DeletionRule.kernel_apply



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
open FD1D.SupplyConfiguration
variable {L m : ℕ}
namespace FD1D.SupplyConfiguration
theorem _root_.solution
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (R : DeletionRule (DyadicNode L) m)
    (hmass : ∀ i, q.leafMass i = R.prob C.countState i)
    (y : InventoryState (DyadicNode L) m) :
    (∑ deleted, ∑ arrived,
      if InventoryState.move C.countState deleted arrived = y then
        (q.selectedIndexLaw hq).mass deleted *
          (1 / Fintype.card (DyadicNode L) : ℝ)
      else 0) =
      R.kernel C.countState y := by
  rw [DeletionRule.kernel_apply]
  simp_rw [q.selectedIndexLaw_mass hq, hmass]
end FD1D.SupplyConfiguration
