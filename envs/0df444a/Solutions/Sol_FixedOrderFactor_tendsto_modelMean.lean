-- Prove2me | solution 1 for FixedOrderFactor.tendsto_modelMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:15.570601+00:00
-- url     : https://prove2.me/submissions/c4afbd6d-246e-4d2e-b9aa-49306ebf917e

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_tendsto_modelMean__e26385be2e3a


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) :=
  tendsto_modelMean' N hr
end FixedOrderFactor
