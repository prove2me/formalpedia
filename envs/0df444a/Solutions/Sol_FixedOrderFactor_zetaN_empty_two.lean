-- Prove2me | solution 1 for FixedOrderFactor.zetaN_empty_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:08.97955+00:00
-- url     : https://prove2.me/submissions/6c932e5c-a718-46c6-805d-d84d5cfc9ae1

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_zetaN_empty_eq

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : zetaN ∅ 2 = π ^ 2 / 6 := by
  rw [zetaN_empty_eq (by norm_num), hasSum_zeta_two.tsum_eq]
end FixedOrderFactor
