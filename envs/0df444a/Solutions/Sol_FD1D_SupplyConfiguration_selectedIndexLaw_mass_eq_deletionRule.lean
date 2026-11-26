-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedIndexLaw_mass_eq_deletionRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:34.163561+00:00
-- url     : https://prove2.me/submissions/4dd86e50-ac13-4d2f-bcba-d3f6c0d90f77

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Spatial

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
    (i : DyadicNode L) :
    (q.selectedIndexLaw hq).mass i = R.prob C.countState i := by
  rw [q.selectedIndexLaw_mass hq, hmass i]
end FD1D.SupplyConfiguration
