-- Prove2me | solution 1 for FixedOrderFactor.summable_pairTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:51.170182+00:00
-- url     : https://prove2.me/submissions/16973a23-0c7a-400e-822f-ac5d056550d2

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal
public import Theorems.Thm_FixedOrderFactor_pairTerm_nonneg
public import Theorems.Thm_FixedOrderFactor_summable_prod_zterm
public import Theorems.Thm_FixedOrderFactor_pairTerm_le

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Summable (pairTerm N r) :=
  Summable.of_nonneg_of_le (pairTerm_nonneg N r) (pairTerm_le N r) (summable_prod_zterm N hr hr)
end FixedOrderFactor
