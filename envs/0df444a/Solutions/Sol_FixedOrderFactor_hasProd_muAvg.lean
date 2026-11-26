-- Prove2me | solution 1 for FixedOrderFactor.hasProd_muAvg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:13.2288+00:00
-- url     : https://prove2.me/submissions/b111cfe3-596c-4b94-adae-cb38bc65bf9d

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) :=
  hasProd_muAvg' N hr
end FixedOrderFactor
