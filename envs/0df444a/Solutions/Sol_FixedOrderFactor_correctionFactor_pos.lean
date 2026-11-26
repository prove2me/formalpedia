-- Prove2me | solution 1 for FixedOrderFactor.correctionFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:00.792647+00:00
-- url     : https://prove2.me/submissions/2923030d-ef9d-48c2-abb9-86d79594dd7e

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    0 < correctionFactor N r := lt_trans one_pos (one_lt_correctionFactor' N hr)
end FixedOrderFactor
