-- Prove2me | solution 1 for FixedOrderFactor.tendsto_correctionFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:09:13.135531+00:00
-- url     : https://prove2.me/submissions/11d2a38d-fc99-4505-b5af-f0e9564b65fb

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_tendsto_correctionFactor__cb9cd39b5893


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) :
    Tendsto (fun r => correctionFactor N r) atTop (𝓝 1) :=
  tendsto_correctionFactor' N
end FixedOrderFactor
