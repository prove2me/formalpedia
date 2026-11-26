-- Prove2me | solution 1 for FixedOrderFactor.hasProd_correctionFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:05.787875+00:00
-- url     : https://prove2.me/submissions/c79de5e8-d11c-4ff8-9789-8bb8bb476fbc

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) :=
  hasProd_correctionFactor' N hr
end FixedOrderFactor
