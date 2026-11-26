-- Prove2me | solution 1 for FixedOrderFactor.summable_norm_zterm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:24.769293+00:00
-- url     : https://prove2.me/submissions/26af1498-ef84-425c-bdf2-7c7c8a9323f6

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
public import Theorems.Thm_FixedOrderFactor_zterm_nonneg
public import Theorems.Thm_FixedOrderFactor_summable_zetaN_terms


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n => ‖zterm N s n‖) :=
  Summable.congr (summable_zetaN_terms N hs : Summable (zterm N s))
    (fun n => (Real.norm_of_nonneg (zterm_nonneg N s n)).symm)
end FixedOrderFactor
