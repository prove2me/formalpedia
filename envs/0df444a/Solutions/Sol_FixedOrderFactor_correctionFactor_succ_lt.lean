-- Prove2me | solution 1 for FixedOrderFactor.correctionFactor_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:09:08.523373+00:00
-- url     : https://prove2.me/submissions/2554fe1e-dba6-4d07-baae-84eebf72ea15

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_succ_lt__e966261d1908


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r :=
  correctionFactor_succ_lt' N hr
end FixedOrderFactor
