-- Prove2me | solution 1 for FD1D.SupplyConfiguration.countState_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:11.201797+00:00
-- url     : https://prove2.me/submissions/06ebcca8-47b7-4448-97a0-0b1aa7bc1318

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
theorem _root_.solution (C : SupplyConfiguration L m) (i : DyadicNode L) :
    C.countState.1 i = C.leafCount i :=
  rfl
end FD1D.SupplyConfiguration
