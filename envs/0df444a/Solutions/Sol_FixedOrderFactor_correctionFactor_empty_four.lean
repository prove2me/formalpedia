-- Prove2me | solution 1 for FixedOrderFactor.correctionFactor_empty_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:35.212785+00:00
-- url     : https://prove2.me/submissions/1d8e65f8-0733-43b0-aadc-7aa971c88f34

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be
public import Theorems.Thm_P2M_FixedOrderFactor_bernoulli_four__5ba47d16df65
public import Theorems.Thm_P2M_FixedOrderFactor_bernoulli_eight__902be8770e09

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution : correctionFactor ∅ 4 = 7 / 6 := by
  have := correctionFactor_even' (k := 2) (by norm_num)
  norm_num [bernoulli_four', bernoulli_eight', Nat.choose] at this
  rw [this]
end FixedOrderFactor
