-- Prove2me | solution 1 for FD1D.SupplyConfiguration.representative_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:38:14.405691+00:00
-- url     : https://prove2.me/submissions/fa23fdf6-ca31-4f54-bdfc-47700c930ea7

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
theorem _root_.solution (C : SupplyConfiguration L m) (fallback : Fin m)
    (i : DyadicNode L) (h : ∃ j, C.leaf j = i) :
    C.leaf (C.representative fallback i) = i := by
  rw [representative, dif_pos h]
  exact Classical.choose_spec h
end FD1D.SupplyConfiguration
