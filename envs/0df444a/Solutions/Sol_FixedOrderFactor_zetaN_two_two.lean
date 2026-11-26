-- Prove2me | solution 1 for FixedOrderFactor.zetaN_two_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:57.572215+00:00
-- url     : https://prove2.me/submissions/fba5ac67-5603-47a8-9457-70be9714d7e9

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_zetaN_empty_two
public import Theorems.Thm_FixedOrderFactor_zetaN_eq


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : zetaN {two} 2 = π ^ 2 / 8 := by
  rw [zetaN_eq _ (le_refl 2), zetaN_empty_two, Finset.prod_singleton]
  simp [two]; ring
end FixedOrderFactor
