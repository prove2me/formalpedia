-- Prove2me | solution 1 for FD1D.SupplyConfiguration.selectedSupplyPoint_mem_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:49.955587+00:00
-- url     : https://prove2.me/submissions/e0125fcd-ed82-43b8-8e05-c812b3d189c7

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
    (q : DyadicMass L) (fallback : Fin m) (u : ℝ) :
    C.selectedSupplyPoint q fallback u ∈ Icc (0 : ℝ) 1 :=
  C.location_mem_unit _
end FD1D.SupplyConfiguration
