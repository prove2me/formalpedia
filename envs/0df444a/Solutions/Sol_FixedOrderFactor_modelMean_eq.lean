-- Prove2me | solution 1 for FixedOrderFactor.modelMean_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:03.17454+00:00
-- url     : https://prove2.me/submissions/ddb3fa47-e60e-4c2b-ac27-87532544cc54

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_modelMean_eq__bf3f86029979


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) :=
  modelMean_eq' r S
end FixedOrderFactor
