-- Prove2me | solution 1 for FixedOrderFactor.sum_orbitAvg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:10:50.095416+00:00
-- url     : https://prove2.me/submissions/f81b9701-fb28-42b6-9609-697c2f023d39

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_eq_zero__21e3915dbad5


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 1 < s) : ∑ t ∈ Finset.range s, orbitAvg s t = 0 :=
  sum_orbitAvg_eq_zero' hs
end FixedOrderFactor
