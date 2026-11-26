-- Prove2me | solution 1 for FixedOrderFactor.one_lt_correctionFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:51.873983+00:00
-- url     : https://prove2.me/submissions/0d4ec016-0fe1-40bc-8bc5-1d8dc98ac79f

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r :=
  one_lt_correctionFactor' N hr
end FixedOrderFactor
