-- Prove2me | solution 1 for FixedOrderFactor.correctionFactor_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:30.999143+00:00
-- url     : https://prove2.me/submissions/2bdb8acc-ae05-4a74-a2cf-c8749cefb1e4

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) :=
  correctionFactor_eq_mul' N hr
end FixedOrderFactor
