-- Prove2me | solution 1 for FixedOrderFactor.sum_orbitAvg_square_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:12.116993+00:00
-- url     : https://prove2.me/submissions/abfe94cc-ec86-459e-ba11-7a2bc81ae2b3

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_square_finite__b7e0b138be07


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 0 < s) (M a : ℕ) :
    ∑ x ∈ (Finset.range M).filter (fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M),
      ∑ t ∈ Finset.range s, orbitAvg s ((x + 1) * t) = s * sqrtCount M a s :=
  sum_orbitAvg_square_finite' hs M a
end FixedOrderFactor
