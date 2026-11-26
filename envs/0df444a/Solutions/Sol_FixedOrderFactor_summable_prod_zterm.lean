-- Prove2me | solution 1 for FixedOrderFactor.summable_prod_zterm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:21.766463+00:00
-- url     : https://prove2.me/submissions/32ec6055-7923-4bbe-8ba8-e0f5fff0eee5

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
public import Theorems.Thm_FixedOrderFactor_summable_norm_zterm

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    Summable (fun x : ℕ × ℕ => zterm N s x.1 * zterm N t x.2) := by
  exact summable_mul_of_summable_norm (summable_norm_zterm N hs) (summable_norm_zterm N ht)
end FixedOrderFactor
