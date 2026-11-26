-- Prove2me | solution 1 for FixedOrderFactor.card_dualPowers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:56.675578+00:00
-- url     : https://prove2.me/submissions/5e10ad0a-2185-44b3-9500-8d8be377d04d

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : r ∣ p - 1) : Nat.card (dualPowers p r) = r := by
  rw [MulChar.card_subgroupOrderIsoSubgroupMulChar, ← Subgroup.index_eq_card,
    IsCyclic.index_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime Fact.out]
  exact Nat.gcd_eq_right hr
end FixedOrderFactor
