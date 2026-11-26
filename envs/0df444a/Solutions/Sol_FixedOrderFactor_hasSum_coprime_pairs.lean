-- Prove2me | solution 1 for FixedOrderFactor.hasSum_coprime_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:21.179147+00:00
-- url     : https://prove2.me/submissions/1120a502-bbd8-4e3f-9881-a2ee68a712a8

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_hasSum_coprime_pairs__627280c9885d


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasSum (fun ab : ℕ × ℕ =>
        if 0 < ab.1 ∧ 0 < ab.2 ∧ Nat.Coprime ab.1 ab.2 ∧ PrimeTo N ab.1 ∧ PrimeTo N ab.2
        then 1 / ((ab.1 * ab.2 : ℕ) : ℝ) ^ r else 0)
      (correctionFactor N r) :=
  hasSum_coprime_pairs' N hr
end FixedOrderFactor
