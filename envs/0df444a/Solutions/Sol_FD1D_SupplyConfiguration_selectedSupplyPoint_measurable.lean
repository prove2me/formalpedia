-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedSupplyPoint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:50.756261+00:00
-- url     : https://prove2.me/submissions/c88ae73c-a0f1-4d5a-96b0-484e0033ffda

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
theorem _root_.solution (C : SupplyConfiguration L m)
    (q : DyadicMass L) (fallback : Fin m) :
    Measurable (C.selectedSupplyPoint q fallback) := by
  exact (measurable_of_finite
    (fun i : DyadicNode L =>
      C.location (C.representative fallback i))).comp
        q.selectedIndex_measurable
end FD1D.SupplyConfiguration
