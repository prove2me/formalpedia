-- Prove2me | solution 1 for FixedOrderFactor.zterm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:53.806533+00:00
-- url     : https://prove2.me/submissions/8a731428-6b89-4084-ab68-6435452b850c

module
public import Definitions.Def_FixedOrderFactor_Values
public import Definitions.Def_FixedOrderFactor_Diagonal

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) (s n : ℕ) : 0 ≤ zterm N s n := by
  unfold zterm; split_ifs <;> positivity
end FixedOrderFactor
